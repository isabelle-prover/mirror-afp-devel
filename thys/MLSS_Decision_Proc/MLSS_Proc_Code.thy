theory MLSS_Proc_Code
  imports MLSS_Proc MLSS_Typing_Urelems "Fresh_Identifiers.Fresh_Nat" "List-Index.List_Index"
begin

section \<open>An Executable Specification of the Procedure\<close>

instantiation nat :: default
begin
definition "default_nat = (0::nat)"

instance ..
end

fun subterms_term_list :: "'a pset_term \<Rightarrow> 'a pset_term list"  where
  "subterms_term_list (\<emptyset> n) = [\<emptyset> n]"
| "subterms_term_list (Var i) = [Var i]"
| "subterms_term_list (t1 \<squnion>\<^sub>s t2) = [t1 \<squnion>\<^sub>s t2] @ subterms_term_list t1 @ subterms_term_list t2"
| "subterms_term_list (t1 \<sqinter>\<^sub>s t2) = [t1 \<sqinter>\<^sub>s t2] @ subterms_term_list t1 @ subterms_term_list t2"
| "subterms_term_list (t1 -\<^sub>s t2) = [t1 -\<^sub>s t2] @ subterms_term_list t1 @ subterms_term_list t2"
| "subterms_term_list (Single t) = [Single t] @ subterms_term_list t"

fun subterms_atom_list :: "'a pset_atom \<Rightarrow> 'a pset_term list"  where
  "subterms_atom_list (t1 \<in>\<^sub>s t2) = subterms_term_list t1 @ subterms_term_list t2"
| "subterms_atom_list (t1 =\<^sub>s t2) = subterms_term_list t1 @ subterms_term_list t2"

fun atoms_list :: "'a pset_fm \<Rightarrow> 'a pset_atom list" where
  "atoms_list (Atom a) = [a]"
| "atoms_list (And p q) = atoms_list p @ atoms_list q"
| "atoms_list (Or p q) = atoms_list p @ atoms_list q"
| "atoms_list (Neg p) = atoms_list p"

definition subterms_fm_list :: "'a pset_fm \<Rightarrow> 'a pset_term list" where
 "subterms_fm_list \<phi> \<equiv> concat (map subterms_atom_list (atoms_list \<phi>))"

definition subterms_branch_list :: "'a branch \<Rightarrow> 'a pset_term list" where
  "subterms_branch_list b \<equiv> concat (map subterms_fm_list b)"

lemma set_subterms_term_list[simp]:
  "set (subterms_term_list t) = subterms t"
  by (induction t) auto

lemma set_subterms_atom_list[simp]:
  "set (subterms_atom_list t) = subterms t"
  by (cases t) auto

lemma set_atoms_list[simp]:
  "set (atoms_list \<phi>) = atoms \<phi>"
  by (induction \<phi>) auto

lemma set_subterms_fm_list[simp]:
  "set (subterms_fm_list \<phi>) = subterms_fm \<phi>"
  unfolding subterms_fm_list_def subterms_fm_def by simp

lemma set_subterms_branch_list[simp]:
  "set (subterms_branch_list b) = subterms b"
  unfolding subterms_branch_list_def subterms_branch_def by simp

fun lexpand_fm1 :: "'a branch \<Rightarrow> 'a pset_fm \<Rightarrow> 'a branch list" where
  "lexpand_fm1 b (And p q) = [[p, q]]"
| "lexpand_fm1 b (Neg (Or p q)) = [[Neg p, Neg q]]"
| "lexpand_fm1 b (Or p q) =
    (if Neg p \<in> set b then [[q]] else []) @
    (if Neg q \<in> set b then [[p]] else [])"
| "lexpand_fm1 b (Neg (And p q)) =
    (if p \<in> set b then [[Neg q]] else []) @
    (if q \<in> set b then [[Neg p]] else [])"
| "lexpand_fm1 b (Neg (Neg p)) = [[p]]"
| "lexpand_fm1 b _ = []"

definition "lexpand_fm b \<equiv> concat (map (lexpand_fm1 b) b)"

lemma lexpand_fm_if_lexpands_fm:
  "lexpands_fm b' b \<Longrightarrow> b' \<in> set (lexpand_fm b)"
  apply(induction rule: lexpands_fm.induct)
        apply(force simp: lexpand_fm_def)+
  done

lemma lexpands_fm_if_lexpand_fm1: 
  "b' \<in> set (lexpand_fm1 b p) \<Longrightarrow> p \<in> set b \<Longrightarrow> lexpands_fm b' b"
  apply(induction b p rule: lexpand_fm1.induct)
        apply(auto simp: lexpands_fm.intros)
  done

lemma lexpands_fm_if_lexpand_fm:
  "b' \<in> set (lexpand_fm b) \<Longrightarrow> lexpands_fm b' b"
  using lexpands_fm_if_lexpand_fm1 unfolding lexpand_fm_def by auto

fun lexpand_un1 :: "'a branch \<Rightarrow> 'a pset_fm \<Rightarrow> 'a branch list" where
  "lexpand_un1 b (AF (s \<in>\<^sub>s t)) =
    [[AF (s \<in>\<^sub>s t \<squnion>\<^sub>s t1)]. AF (s' \<in>\<^sub>s t1) \<leftarrow> b, s' = s, t \<squnion>\<^sub>s t1 \<in> subterms (last b)] @
    [[AF (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t)]. AF (s' \<in>\<^sub>s t1) \<leftarrow> b, s' = s, t1 \<squnion>\<^sub>s t \<in> subterms (last b)] @ 
    (case t of
      t1 \<squnion>\<^sub>s t2 \<Rightarrow> [[AF (s \<in>\<^sub>s t1), AF (s \<in>\<^sub>s t2)]]
    | _ \<Rightarrow> [])"
| "lexpand_un1 b (AT (s \<in>\<^sub>s t)) =
    [[AT (s \<in>\<^sub>s t \<squnion>\<^sub>s t2)]. t1 \<squnion>\<^sub>s t2 \<leftarrow> subterms_fm_list (last b), t1 = t] @
    [[AT (s \<in>\<^sub>s t1 \<squnion>\<^sub>s t)]. t1 \<squnion>\<^sub>s t2 \<leftarrow> subterms_fm_list (last b), t2 = t] @
    (case t of
      t1 \<squnion>\<^sub>s t2 \<Rightarrow> (if AF (s \<in>\<^sub>s t1) \<in> set b then [[AT (s \<in>\<^sub>s t2)]] else []) @
                  (if AF (s \<in>\<^sub>s t2) \<in> set b then [[AT (s \<in>\<^sub>s t1)]] else [])
    | _ \<Rightarrow> [])"
| "lexpand_un1 _ _ = []"

definition "lexpand_un b \<equiv> concat (map (lexpand_un1 b) b)"

lemma lexpand_un_if_lexpands_un:
  "lexpands_un b' b \<Longrightarrow> b' \<in> set (lexpand_un b)"
  apply(induction rule: lexpands_un.induct)
       apply(force simp: lexpand_un_def)+
  done

lemma lexpands_un_if_lexpand_un1:
  "b' \<in> set (lexpand_un1 b l) \<Longrightarrow> l \<in> set b \<Longrightarrow> lexpands_un b' b"
  apply(induction b l rule: lexpand_un1.induct)
          apply(auto simp: lexpands_un.intros)
  done

lemma lexpands_un_if_lexpand_un:
  "b' \<in> set (lexpand_un b) \<Longrightarrow> lexpands_un b' b"
  unfolding lexpand_un_def using lexpands_un_if_lexpand_un1 by auto

fun lexpand_int1 :: "'a branch \<Rightarrow> 'a pset_fm \<Rightarrow> 'a branch list" where
  "lexpand_int1 b (AT (s \<in>\<^sub>s t)) =
    [[AT (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t)]. AT (s' \<in>\<^sub>s t1) \<leftarrow> b, s' = s, t1 \<sqinter>\<^sub>s t \<in> subterms (last b)] @
    [[AT (s \<in>\<^sub>s t \<sqinter>\<^sub>s t2)]. AT (s' \<in>\<^sub>s t2) \<leftarrow> b, s' = s, t \<sqinter>\<^sub>s t2 \<in> subterms (last b)] @
    (case t of t1 \<sqinter>\<^sub>s t2 \<Rightarrow> [[AT (s \<in>\<^sub>s t1), AT (s \<in>\<^sub>s t2)]] | _ \<Rightarrow> [])"
| "lexpand_int1 b (AF (s \<in>\<^sub>s t)) =
    [[AF (s \<in>\<^sub>s t \<sqinter>\<^sub>s t2)]. t1 \<sqinter>\<^sub>s t2 \<leftarrow> subterms_fm_list (last b), t1 = t] @
    [[AF (s \<in>\<^sub>s t1 \<sqinter>\<^sub>s t)]. t1 \<sqinter>\<^sub>s t2 \<leftarrow> subterms_fm_list (last b), t2 = t] @
    (case t of
      t1 \<sqinter>\<^sub>s t2 \<Rightarrow> (if AT (s \<in>\<^sub>s t1) \<in> set b then [[AF (s \<in>\<^sub>s t2)]] else []) @
                  (if AT (s \<in>\<^sub>s t2) \<in> set b then [[AF (s \<in>\<^sub>s t1)]] else [])
    | _ \<Rightarrow> [])"
| "lexpand_int1 _ _ = []"

definition "lexpand_int b \<equiv> concat (map (lexpand_int1 b) b)"

lemma lexpand_int_if_lexpands_int:
  "lexpands_int b' b \<Longrightarrow> b' \<in> set (lexpand_int b)"
  apply(induction rule: lexpands_int.induct)
       apply(force simp: lexpand_int_def)+
  done

lemma lexpands_int_if_lexpand_int1:
  "b' \<in> set (lexpand_int1 b l) \<Longrightarrow> l \<in> set b \<Longrightarrow> lexpands_int b' b"
  apply(induction b l rule: lexpand_int1.induct)
          apply(auto simp: lexpands_int.intros)
  done

lemma lexpands_int_if_lexpand_int:
  "b' \<in> set (lexpand_int b) \<Longrightarrow> lexpands_int b' b"
  unfolding lexpand_int_def using lexpands_int_if_lexpand_int1 by auto

fun lexpand_diff1 :: "'a branch \<Rightarrow> 'a pset_fm \<Rightarrow> 'a branch list" where
  "lexpand_diff1 b (AT (s \<in>\<^sub>s t)) =
    [[AT (s \<in>\<^sub>s t -\<^sub>s t2)]. AF (s' \<in>\<^sub>s t2) \<leftarrow> b, s' = s, t -\<^sub>s t2 \<in> subterms (last b)] @
    [[AF (s \<in>\<^sub>s t1 -\<^sub>s t)]. AF (s' \<in>\<^sub>s t1) \<leftarrow> b, s' = s, t1 -\<^sub>s t \<in> subterms (last b)] @
    [[AF (s \<in>\<^sub>s t1 -\<^sub>s t)]. t1 -\<^sub>s t2 \<leftarrow> subterms_fm_list (last b), t2 = t] @
    (case t of t1 -\<^sub>s t2 \<Rightarrow> [[AT (s \<in>\<^sub>s t1), AF (s \<in>\<^sub>s t2)]] | _ \<Rightarrow> [])"
| "lexpand_diff1 b (AF (s \<in>\<^sub>s t)) =
    [[AF (s \<in>\<^sub>s t -\<^sub>s t2)]. t1 -\<^sub>s t2 \<leftarrow> subterms_fm_list (last b), t1 = t] @
    (case t of
      t1 -\<^sub>s t2 \<Rightarrow> (if AT (s \<in>\<^sub>s t1) \<in> set b then [[AT (s \<in>\<^sub>s t2)]] else []) @
                  (if AF (s \<in>\<^sub>s t2) \<in> set b then [[AF (s \<in>\<^sub>s t1)]] else [])
    | _ \<Rightarrow> [])"
| "lexpand_diff1 _ _ = []"

definition "lexpand_diff b \<equiv> concat (map (lexpand_diff1 b) b)"

lemma lexpand_diff_if_lexpands_diff:
  "lexpands_diff b' b \<Longrightarrow> b' \<in> set (lexpand_diff b)"
  apply(induction rule: lexpands_diff.induct)
       apply(force simp: lexpand_diff_def)+
  done

lemma lexpands_diff_if_lexpand_diff1:
  "b' \<in> set (lexpand_diff1 b l) \<Longrightarrow> l \<in> set b \<Longrightarrow> lexpands_diff b' b"
  apply(induction b l rule: lexpand_diff1.induct)
          apply(auto simp: lexpands_diff.intros)
  done

lemma lexpands_diff_if_lexpand_diff:
  "b' \<in> set (lexpand_diff b) \<Longrightarrow> lexpands_diff b' b"
  unfolding lexpand_diff_def using lexpands_diff_if_lexpand_diff1 by auto

fun lexpand_single1 :: "'a branch \<Rightarrow> 'a pset_fm \<Rightarrow> 'a branch list" where
  "lexpand_single1 b (AT (s \<in>\<^sub>s Single t)) = [[AT (s =\<^sub>s t)]]"
| "lexpand_single1 b (AF (s \<in>\<^sub>s Single t)) = [[AF (s =\<^sub>s t)]]"
| "lexpand_single1 _ _ = []"

definition "lexpand_single b \<equiv>
  [[AT (t1 \<in>\<^sub>s Single t1)]. Single t1 \<leftarrow> subterms_fm_list (last b)] @
  concat (map (lexpand_single1 b) b)"

lemma lexpand_single_if_lexpands_single:
  "lexpands_single b' b \<Longrightarrow> b' \<in> set (lexpand_single b)"
  apply(induction rule: lexpands_single.induct)
       apply(force simp: lexpand_single_def)+
  done

lemma lexpands_single_if_lexpand_single1:
  "b' \<in> set (lexpand_single1 b l) \<Longrightarrow> l \<in> set b \<Longrightarrow> lexpands_single b' b"
  apply(induction b l rule: lexpand_single1.induct)
          apply(auto simp: lexpands_single.intros)
  done

lemma lexpands_single_if_lexpand_single:
  "b' \<in> set (lexpand_single b) \<Longrightarrow> lexpands_single b' b"
  unfolding lexpand_single_def using lexpands_single_if_lexpand_single1
  by (auto simp: lexpands_single.intros)

fun lexpand_eq1 :: "'a branch \<Rightarrow> 'a pset_fm \<Rightarrow> 'a branch list" where
  "lexpand_eq1 b (AT (t1 =\<^sub>s t2)) =
    [[AT (subst_tlvl t1 t2 a)]. AT a \<leftarrow> b, t1 \<in> tlvl_terms a] @
    [[AF (subst_tlvl t1 t2 a)]. AF a \<leftarrow> b, t1 \<in> tlvl_terms a] @
    [[AT (subst_tlvl t2 t1 a)]. AT a \<leftarrow> b, t2 \<in> tlvl_terms a] @
    [[AF (subst_tlvl t2 t1 a)]. AF a \<leftarrow> b, t2 \<in> tlvl_terms a]"
| "lexpand_eq1 b _ = []"

definition "lexpand_eq b \<equiv>
  [[AF (s =\<^sub>s s')]. AT (s \<in>\<^sub>s t) \<leftarrow> b, AF (s' \<in>\<^sub>s t') \<leftarrow> b, t' = t] @
  concat (map (lexpand_eq1 b) b)"

lemma lexpand_eq_if_lexpands_eq:
  "lexpands_eq b' b \<Longrightarrow> b' \<in> set (lexpand_eq b)"
  apply(induction rule: lexpands_eq.induct)
       apply(force simp: lexpand_eq_def)+
  done

lemma lexpands_eq_if_lexpand_eq1:
  "b' \<in> set (lexpand_eq1 b l) \<Longrightarrow> l \<in> set b \<Longrightarrow> lexpands_eq b' b"
  apply(induction b l rule: lexpand_eq1.induct)
          apply(auto simp: lexpands_eq.intros)
  done

lemma lexpands_eq_if_lexpand_eq:
  "b' \<in> set (lexpand_eq b) \<Longrightarrow> lexpands_eq b' b"
  unfolding lexpand_eq_def using lexpands_eq_if_lexpand_eq1
  by (auto simp: lexpands_eq.intros)

definition "lexpand b \<equiv>
  lexpand_fm b @
  lexpand_un b @ lexpand_int b @ lexpand_diff b @ 
  lexpand_single b @ lexpand_eq b"

lemma lexpand_if_lexpands:
  "lexpands b' b \<Longrightarrow> b' \<in> set (lexpand b)"
  apply(induction rule: lexpands.induct)
  unfolding lexpand_def
  using lexpand_fm_if_lexpands_fm
  using lexpand_un_if_lexpands_un lexpand_int_if_lexpands_int lexpand_diff_if_lexpands_diff
  using lexpand_single_if_lexpands_single lexpand_eq_if_lexpands_eq
  by fastforce+

lemma lexpands_if_lexpand:
  "b' \<in> set (lexpand b) \<Longrightarrow> lexpands b' b"
  unfolding lexpand_def
  using lexpands_fm_if_lexpand_fm
  using lexpands_un_if_lexpand_un lexpands_int_if_lexpand_int lexpands_diff_if_lexpand_diff
  using lexpands_single_if_lexpand_single lexpands_eq_if_lexpand_eq
  using lexpands.intros by fastforce

fun bexpand_nowit1 :: "'a branch \<Rightarrow> 'a pset_fm \<Rightarrow> 'a branch list list" where
  "bexpand_nowit1 b (Or p q) =
    (if p \<notin> set b \<and> Neg p \<notin> set b then [[[p], [Neg p]]] else [])"
| "bexpand_nowit1 b (Neg (And p q)) =
    (if Neg p \<notin> set b \<and> p \<notin> set b then [[[Neg p], [p]]] else [])"
| "bexpand_nowit1 b (AT (s \<in>\<^sub>s t)) =
    [[[AT (s \<in>\<^sub>s t2)], [AF (s \<in>\<^sub>s t2)]]. t' \<sqinter>\<^sub>s t2 \<leftarrow> subterms_fm_list (last b), t' = t,
                                       AT (s \<in>\<^sub>s t2) \<notin> set b, AF (s \<in>\<^sub>s t2) \<notin> set b] @
    [[[AT (s \<in>\<^sub>s t2)], [AF (s \<in>\<^sub>s t2)]]. t' -\<^sub>s t2 \<leftarrow> subterms_fm_list (last b), t' = t,
                                       AT (s \<in>\<^sub>s t2) \<notin> set b, AF (s \<in>\<^sub>s t2) \<notin> set b] @
    (case t of
      t1 \<squnion>\<^sub>s t2 \<Rightarrow>
        (if t1 \<squnion>\<^sub>s t2 \<in> subterms (last b) \<and> AT (s \<in>\<^sub>s t1) \<notin> set b \<and> AF (s \<in>\<^sub>s t1) \<notin> set b
          then [[[AT (s \<in>\<^sub>s t1)], [AF (s \<in>\<^sub>s t1)]]] else [])
    | _ \<Rightarrow> [])"
| "bexpand_nowit1 b _ = []"

definition "bexpand_nowit b \<equiv> concat (map (bexpand_nowit1 b) b)"

lemma bexpand_nowit_if_bexpands_nowit:
  "bexpands_nowit bs' b \<Longrightarrow> bs' \<in> set ` set (bexpand_nowit b)"
  apply(induction rule: bexpands_nowit.induct)
       apply(force simp: bexpand_nowit_def)+
  done

lemma bexpands_nowit_if_bexpand_nowit1:
  "bs' \<in> set ` set (bexpand_nowit1 b l) \<Longrightarrow> l \<in> set b \<Longrightarrow> bexpands_nowit bs' b"
  apply(induction b l rule: bexpand_nowit1.induct)
          apply(auto simp: bexpands_nowit.intros)
  done

lemma bexpands_nowit_if_bexpand_nowit:
  "bs' \<in> set ` set (bexpand_nowit b) \<Longrightarrow> bexpands_nowit bs' b"
  unfolding bexpand_nowit_def using bexpands_nowit_if_bexpand_nowit1
  by (auto simp: bexpands_nowit.intros)

definition "name_subterm \<phi> \<equiv> index (subterms_fm_list \<phi>)"

lemma inj_on_name_subterm_subterms:
  "inj_on (name_subterm \<phi>) (subterms \<phi>)"
  unfolding name_subterm_def
  by (intro inj_on_index2) simp

abbreviation "solve_constraints \<phi> \<equiv>
  MLSS_Suc_Theory.solve (MLSS_Suc_Theory.elim_NEq_Zero (constrs_fm (name_subterm \<phi>) \<phi>))"

definition "urelem_code \<phi> t \<equiv>
  (case solve_constraints \<phi> of
    Some ss \<Rightarrow> MLSS_Suc_Theory.assign ss (name_subterm \<phi> t) = 0
  | None \<Rightarrow> False)"

lemma urelem_code_if_mem_subterms:
  assumes "t \<in> subterms \<phi>"
  shows "urelem \<phi> t \<longleftrightarrow> urelem_code \<phi> t"
proof -
  note urelem_iff_assign_eq_0[OF _ assms] not_types_fm_if_solve_eq_None
  note solve_correct = this[OF inj_on_name_subterm_subterms]
  then show ?thesis
    unfolding urelem_def urelem_code_def
    by (auto split: option.splits)
qed

fun bexpand_wit1 :: "('a::{fresh,default}) branch \<Rightarrow> 'a pset_fm \<Rightarrow> 'a branch list list" where
  "bexpand_wit1 b (AF (t1 =\<^sub>s t2)) =
    (if t1 \<in> subterms (last b) \<and> t2 \<in> subterms (last b) \<and>
        (\<forall>t \<in> set b. case t of AT (x \<in>\<^sub>s t1') \<Rightarrow> t1' = t1 \<longrightarrow> AF (x \<in>\<^sub>s t2) \<notin> set b | _ \<Rightarrow> True) \<and>
        (\<forall>t \<in> set b. case t of AT (x \<in>\<^sub>s t2') \<Rightarrow> t2' = t2 \<longrightarrow> AF (x \<in>\<^sub>s t1) \<notin> set b | _ \<Rightarrow> True) \<and>
        \<not> urelem_code (last b) t1 \<and> \<not> urelem_code (last b) t2
      then
        (let x = fresh (vars b) default
         in [[[AT (Var x \<in>\<^sub>s t1), AF (Var x \<in>\<^sub>s t2)],
              [AT (Var x \<in>\<^sub>s t2), AF (Var x \<in>\<^sub>s t1)]]])
      else [])"
| "bexpand_wit1 b _ = []"

definition "bexpand_wit b \<equiv> concat (map (bexpand_wit1 b) b)"

lemma Not_Ex_wit_code:
  "(\<nexists>x. AT (x \<in>\<^sub>s t1) \<in> set b \<and> AF (x \<in>\<^sub>s t2) \<in> set b)
    \<longleftrightarrow> (\<forall>fm \<in> set b. case fm of
                        AT (x \<in>\<^sub>s t') \<Rightarrow> t' = t1 \<longrightarrow> AF (x \<in>\<^sub>s t2) \<notin> set b
                      | _ \<Rightarrow> True)"
  by (auto split: fm.splits pset_atom.splits)

lemma bexpand_wit1_if_bexpands_wit:
  assumes "bexpands_wit t1 t2 (fresh (vars b) default) bs' b"
  shows "bs' \<in> set ` set (bexpand_wit1 b (AF (t1 =\<^sub>s t2)))"
proof -
  from bexpands_witD[OF assms] show ?thesis
    by (simp add: Let_def urelem_code_if_mem_subterms Not_Ex_wit_code[symmetric])
qed

lemma bexpand_wit_if_bexpands_wit:
  assumes "bexpands_wit t1 t2 (fresh (vars b) default) bs' b"
  shows "bs' \<in> set ` set (bexpand_wit b)"
  using assms(1)[THEN bexpand_wit1_if_bexpands_wit] bexpands_witD(2)[OF assms(1)]
  unfolding bexpand_wit_def 
  by (auto simp del: bexpand_wit1.simps(1))
  
lemma bexpands_wit_if_bexpand_wit1:
  "b' \<in> set ` set (bexpand_wit1 b l) \<Longrightarrow> l \<in> set b \<Longrightarrow> (\<exists>t1 t2 x. bexpands_wit t1 t2 x b' b)"
proof(induction b l rule: bexpand_wit1.induct)
  case (1 b t1 t2)
  show ?case
    apply(rule exI[where ?x=t1], rule exI[where ?x=t2],
          rule exI[where ?x="fresh (vars b) default"])
    using 1
    by (auto simp: Let_def bexpands_wit.simps finite_vars_branch[THEN fresh_notIn]
                   Not_Ex_wit_code[symmetric] urelem_code_if_mem_subterms)
qed auto
    
lemma bexpands_wit_if_bexpand_wit:
  "bs' \<in> set ` set (bexpand_wit b) \<Longrightarrow> (\<exists>t1 t2 x. bexpands_wit t1 t2 x bs' b)"
proof -
  assume "bs' \<in> set ` set (bexpand_wit b)"
  then obtain l where "bs' \<in> set ` set (bexpand_wit1 b l)" "l \<in> set b" 
    unfolding bexpand_wit_def by auto
  from bexpands_wit_if_bexpand_wit1[OF this] show ?thesis .
qed
                                
definition "bexpand b \<equiv> bexpand_nowit b @ bexpand_wit b"

lemma bexpands_if_bexpand:
  "bs' \<in> set ` set (bexpand b) \<Longrightarrow> bexpands bs' b"
  unfolding bexpand_def
  using bexpands_nowit_if_bexpand_nowit bexpands_wit_if_bexpand_wit
  by (metis bexpands.intros UnE image_Un set_append)

lemma Not_bexpands_if_bexpand_empty:
  assumes "bexpand b = []"
  shows "\<not> bexpands bs' b"
proof
  assume "bexpands bs' b"
  then show False
    using assms
  proof (induction rule: bexpands.induct)
    case (1 bs' b)
    with bexpand_nowit_if_bexpands_nowit[OF this(1)] show ?case
      unfolding bexpand_def by simp
  next
    case (2 t1 t2 x bs' b)
    note fresh_notIn[OF finite_vars_branch, of b]
    with 2 obtain bs'' where "bexpands_wit t1 t2 (fresh (vars b) default) bs'' b"
      by (auto simp: bexpands_wit.simps)
    from 2 bexpand_wit_if_bexpands_wit[OF this] show ?case
      by (simp add: bexpand_def)
  qed
qed

lemma lin_sat_code:
  "lin_sat b \<longleftrightarrow> filter (\<lambda>b'. \<not> set b' \<subseteq> set b) (lexpand b) = []"
  unfolding lin_sat_def
  using lexpand_if_lexpands lexpands_if_lexpand
  by (force simp: filter_empty_conv)

lemma sat_code:
  "sat b \<longleftrightarrow> lin_sat b \<and> bexpand b = []"
  using Not_bexpands_if_bexpand_empty bexpands_if_bexpand
  unfolding sat_def
  by (metis imageI list.set_intros(1) list_exhaust2)

fun bclosed_code1 :: "'a branch \<Rightarrow> 'a pset_fm \<Rightarrow> bool" where
  "bclosed_code1 b (Neg \<phi>) \<longleftrightarrow>
    \<phi> \<in> set b \<or>
    (case \<phi> of Atom (t1 =\<^sub>s t2) \<Rightarrow> t1 = t2 | _ \<Rightarrow> False)"
| "bclosed_code1 b (AT (_ \<in>\<^sub>s \<emptyset> _)) \<longleftrightarrow> True"
| "bclosed_code1 _ _ \<longleftrightarrow> False"

definition "bclosed_code b \<equiv> (\<exists>t \<in> set b. bclosed_code1 b t)"

lemma bclosed_code_if_bclosed:
  assumes "bclosed b" "wf_branch b" "v \<turnstile> last b"
  shows "bclosed_code b"
  using assms
proof(induction rule: bclosed.induct)
  case (contr \<phi> b)
  then have "bclosed_code1 b (Neg \<phi>)"
    by auto
  with contr show ?case
    unfolding bclosed_code_def by blast
next
  case (memEmpty t n b)
  then have "bclosed_code1 b (AT (t \<in>\<^sub>s \<emptyset> n))"
    by auto
  with memEmpty show ?case
    unfolding bclosed_code_def by blast
next
  case (neqSelf t b)
  then have "bclosed_code1 b (AF (t =\<^sub>s t))"
    by auto
  with neqSelf show ?case
    unfolding bclosed_code_def by blast
next
  case (memberCycle cs b)
  then show ?case
    by (auto simp: bclosed_code_def dest: no_member_cycle_if_types_last)
qed

lemma bclosed_if_bclosed_code1:
  "bclosed_code1 b l \<Longrightarrow> l \<in> set b \<Longrightarrow> bclosed b"
  by (induction rule: bclosed_code1.induct)
     (auto simp: bclosed.intros split: fm.splits pset_atom.splits)

lemma bclosed_if_bclosed_code:
  "bclosed_code b \<Longrightarrow> bclosed b"
  unfolding bclosed_code_def using bclosed_if_bclosed_code1 by blast

lemma bclosed_code:
  assumes "wf_branch b" "v \<turnstile> last b"
  shows "bclosed b \<longleftrightarrow> bclosed_code b"
  using assms bclosed_if_bclosed_code bclosed_code_if_bclosed 
  by blast

definition "lexpand_safe b \<equiv>
  case filter (\<lambda>b'. \<not> set b' \<subseteq> set b) (lexpand b) of
    b' # bs' \<Rightarrow> b'
  | [] \<Rightarrow> []"

lemma lexpands_lexpand_safe:
  "\<not> lin_sat b \<Longrightarrow> lexpands (lexpand_safe b) b \<and> set b \<subset> set (lexpand_safe b @ b)"
  unfolding lexpand_safe_def
  by (auto simp: lin_sat_code intro!: lexpands_if_lexpand dest: filter_eq_ConsD split: list.splits)

lemma wf_branch_lexpand_safe:
  assumes "wf_branch b"
  shows "wf_branch (lexpand_safe b @ b)"
proof -
  from assms have "wf_branch (lexpand_safe b @ b)" if "\<not> lin_sat b"
    using that lexpands_lexpand_safe wf_branch_lexpands by metis
  moreover have "wf_branch (lexpand_safe b @ b)" if "lin_sat b"
    using assms that[unfolded lin_sat_code]
    unfolding lexpand_safe_def by simp
  ultimately show ?thesis
    by blast
qed

definition "bexpand_safe b \<equiv>
  case bexpand b of
    bs' # bss' \<Rightarrow> bs'
  | [] \<Rightarrow> [[]]"

lemma bexpands_bexpand_safe:
  "\<not> sat b \<Longrightarrow> lin_sat b \<Longrightarrow> bexpands (set (bexpand_safe b)) b"
  unfolding bexpand_safe_def
  by (auto simp: sat_code bexpands_if_bexpand split: list.splits)

lemma wf_branch_bexpand_safe:
  assumes "wf_branch b"
  shows "\<forall>b' \<in> set (bexpand_safe b). wf_branch (b' @ b)"
proof -
  note wf_branch_expandss[OF assms expandss.intros(3), OF bexpands_if_bexpand]
  with assms show ?thesis
    unfolding bexpand_safe_def
    by (simp split: list.splits) (metis expandss.intros(1) image_iff list.set_intros(1))
qed

interpretation mlss_naive: mlss_proc lexpand_safe "set o bexpand_safe"
  apply(unfold_locales)
  using lexpands_lexpand_safe bexpands_bexpand_safe by auto

lemma types_pset_fm_code:
  "(\<exists>v. v \<turnstile> \<phi>) \<longleftrightarrow> solve_constraints \<phi> \<noteq> None"
  using not_types_fm_if_solve_eq_None types_pset_fm_assign_solve
  by (meson inj_on_name_subterm_subterms not_Some_eq)

fun foldl_option where
  "foldl_option f a [] = Some a"
| "foldl_option f _ (None # _) = None"
| "foldl_option f a (Some x # xs) = foldl_option f (f a x) xs"

lemma monotone_fold_option_conj[partial_function_mono]:
  "monotone (list_all2 option_ord) option_ord (foldl_option f a)"
proof
  fix xs ys :: "'a option list"
  assume "list_all2 option_ord xs ys"
  then show "option_ord (foldl_option f a xs) (foldl_option f a ys)"
  proof(induction xs ys arbitrary: a rule: list_all2_induct)
    case Nil
    then show ?case by (simp add: option.leq_refl)
  next
    case (Cons xo xos yo yos)
    then consider
        "xo = None" "yo = None"
      | y where "xo = None" "yo = Some y"
      | x y where "xo = Some x" "yo = Some y"
      by (metis flat_ord_def option.exhaust)
    then show ?case
      using Cons
      by cases (simp_all add: option.leq_refl flat_ord_def)
  qed
qed

lemma monotone_map[partial_function_mono]:
  assumes "monotone (list_all2 option_ord) ordb B"
  shows "monotone option.le_fun ordb (\<lambda>h. B (map h xs))"
  using assms
  by (simp add: fun_ord_def list_all2_conv_all_nth monotone_on_def)

partial_function (option) mlss_proc_branch_partial
  :: "('a::{fresh,default}) branch \<Rightarrow> bool option" where
  "mlss_proc_branch_partial b =
    (if \<not> lin_sat b then mlss_proc_branch_partial (lexpand_safe b @ b)
     else if bclosed_code b then Some True
     else if \<not> sat b then
        foldl_option (\<and>) True (map mlss_proc_branch_partial (map (\<lambda>b'. b' @ b) (bexpand_safe b)))
     else Some (bclosed_code b))"

lemma mlss_proc_branch_partial_eq:
  assumes "wf_branch b" "v \<turnstile> last b"
  shows "mlss_proc_branch_partial b = Some (mlss_naive.mlss_proc_branch b)"
    (is "?mlss_part b = Some (?mlss b)")
  using mlss_naive.mlss_proc_branch_dom_if_wf_branch[OF assms(1)] assms
proof(induction rule: mlss_naive.mlss_proc_branch.pinduct)
  case (1 b)
  then have "?mlss_part (lexpand_safe b @ b)
    = Some (mlss_naive.mlss_proc_branch (lexpand_safe b @ b))"
    using wf_branch_lexpand_safe[OF \<open>wf_branch b\<close>] by fastforce
  with 1 show ?case
    by (subst mlss_proc_branch_partial.simps)
       (auto simp: mlss_naive.mlss_proc_branch.psimps)
next
  case (2 b)
  then show ?case
    by (subst mlss_proc_branch_partial.simps)
       (auto simp: mlss_naive.mlss_proc_branch.psimps bclosed_code)
next
  case (3 b)
  then have "?mlss_part (b' @ b) = Some (?mlss (b' @ b))"
    if "b' \<in> set (bexpand_safe b)" for b'
    using that wf_branch_bexpand_safe[OF \<open>wf_branch b\<close>] by fastforce
  then have "map ?mlss_part (map (\<lambda>b'. b' @ b) (bexpand_safe b))
    = map Some (map (\<lambda>b'. (?mlss (b' @ b))) (bexpand_safe b))"
    by simp
  moreover have "foldl_option (\<and>) a (map Some xs) = Some (a \<and> (\<forall>x \<in> set xs. x))" for a xs
    by (induction xs arbitrary: a) auto
  moreover have foldl_option_eq:
    "foldl_option (\<and>) True (map ?mlss_part (map (\<lambda>b'. b' @ b) (bexpand_safe b)))
    = Some (\<forall>b' \<in> set (bexpand_safe b). ?mlss (b' @ b))"
    unfolding calculation by (auto simp: comp_def)
  from 3 show ?case
    by (subst mlss_proc_branch_partial.simps, subst foldl_option_eq)
       (simp add: bclosed_code mlss_naive.mlss_proc_branch.psimps(3))
next
  case (4 b)
  then show ?case
    by (subst mlss_proc_branch_partial.simps)
       (auto simp: mlss_naive.mlss_proc_branch.psimps bclosed_code)
qed

definition "mlss_proc_partial (\<phi> :: nat pset_fm) \<equiv>
  if solve_constraints \<phi> = None then None else mlss_proc_branch_partial [\<phi>]"

lemma mlss_proc_partial_eq_None:
  "mlss_proc_partial \<phi> = None \<Longrightarrow> (\<nexists>v. v \<turnstile> \<phi>)"
  unfolding mlss_proc_partial_def
  using types_pset_fm_code mlss_proc_branch_partial_eq wf_branch_singleton
  by (metis last.simps option.discI)

lemma mlss_proc_partial_complete:
  assumes "mlss_proc_partial \<phi> = Some False"
  shows "\<exists>M. interp I\<^sub>s\<^sub>a M \<phi>"
proof -
  from assms have "\<exists>v. v \<turnstile> \<phi>"
    unfolding mlss_proc_partial_def using types_pset_fm_code by force
  moreover have "\<not> mlss_naive.mlss_proc \<phi>"
    using assms \<open>\<exists>v. v \<turnstile> \<phi>\<close> mlss_proc_branch_partial_eq calculation wf_branch_singleton
    unfolding mlss_naive.mlss_proc_def mlss_proc_partial_def
    by (metis last.simps option.discI option.inject)
  ultimately show ?thesis
    using mlss_naive.mlss_proc_complete by blast
qed

lemma mlss_proc_partial_sound:
  assumes "mlss_proc_partial \<phi> = Some True"
  shows "\<not> interp I\<^sub>s\<^sub>a M \<phi>"
proof -
  from assms have "\<exists>v. v \<turnstile> \<phi>"
    unfolding mlss_proc_partial_def using types_pset_fm_code by force
  moreover have "mlss_naive.mlss_proc \<phi>"
    using assms \<open>\<exists>v. v \<turnstile> \<phi>\<close> mlss_proc_branch_partial_eq calculation wf_branch_singleton
    unfolding mlss_naive.mlss_proc_def mlss_proc_partial_def
    by (metis last.simps option.discI option.inject)
  ultimately show ?thesis
    using mlss_naive.mlss_proc_sound by blast
qed

declare lin_sat_code[code] sat_code[code]
declare mlss_proc_branch_partial.simps[code]
code_identifier
    code_module MLSS_Calculus \<rightharpoonup> (SML) MLSS_Proc_Code
  | code_module MLSS_Proc \<rightharpoonup> (SML) MLSS_Proc_Code
export_code mlss_proc_partial in SML

end
