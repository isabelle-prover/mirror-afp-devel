header {* Deciding Regular Expression Equivalence (2) *}

theory pEquivalence_Checking
imports Equivalence_Checking
begin

text{* \noindent Similar to theory @{theory Equivalence_Checking}, but
with partial derivatives instead of derivatives. *}

text{* Lifting many notions to sets: *}

definition "Lang R == UN r:R. lang r"
definition "Nullable R == EX r:R. nullable r"
definition "Pderiv a R == UN r:R. pderiv a r"
definition "Atoms R == UN r:R. atoms r"

(* FIXME: rename pderiv_set in Derivatives to Pderiv and drop the one above *)

lemma Atoms_pderiv: "Atoms(pderiv a r) \<subseteq> atoms r"
apply (induct r)
apply (auto simp: Atoms_def UN_subset_iff)
apply (fastforce)+
done

lemma Atoms_Pderiv: "Atoms(Pderiv a R) \<subseteq> Atoms R"
using Atoms_pderiv by (fastforce simp: Atoms_def Pderiv_def)

lemma pderiv_no_occurrence: 
  "x \<notin> atoms r \<Longrightarrow> pderiv x r = {}"
by (induct r) auto

lemma Pderiv_no_occurrence: 
  "x \<notin> Atoms R \<Longrightarrow> Pderiv x R = {}"
by(auto simp:pderiv_no_occurrence Atoms_def Pderiv_def)

lemma Deriv_Lang: "Deriv c (Lang R) = Lang (Pderiv c R)"
by(auto simp: Deriv_pderiv Pderiv_def Lang_def)

type_synonym 'a Rexp_pair = "'a rexp set * 'a rexp set"
type_synonym 'a Rexp_pairs = "'a Rexp_pair list"

definition is_Bisimulation :: "'a list \<Rightarrow> 'a Rexp_pairs \<Rightarrow> bool"
where
"is_Bisimulation as ps =
  (\<forall>(R,S)\<in> set ps. Atoms R \<union> Atoms S \<subseteq> set as \<and>
    (Nullable R \<longleftrightarrow> Nullable S) \<and>
    (\<forall>a\<in>set as. (Pderiv a R, Pderiv a S) \<in> set ps))"

lemma Bisim_Lang_eq:
assumes Bisim: "is_Bisimulation as ps"
assumes "(R, S) \<in> set ps"
shows "Lang R = Lang S"
proof -
  def ps' \<equiv> "({}, {}) # ps"
  from Bisim have Bisim': "is_Bisimulation as ps'"
    by (fastforce simp: ps'_def is_Bisimulation_def UN_subset_iff Pderiv_def Atoms_def)
  let ?R = "\<lambda>K L. (\<exists>(R,S)\<in>set ps'. K = Lang R \<and> L = Lang S)"
  show ?thesis
  proof (rule language_coinduct[where R="?R"])
    from `(R,S) \<in> set ps`
    have "(R,S) \<in> set ps'" by (auto simp: ps'_def)
    thus "?R (Lang R) (Lang S)" by auto
  next
    fix K L assume "?R K L"
    then obtain R S where rs: "(R, S) \<in> set ps'"
      and KL: "K = Lang R" "L = Lang S" by auto
    with Bisim' have "Nullable R \<longleftrightarrow> Nullable S"
      by (auto simp: is_Bisimulation_def)
    thus "[] \<in> K \<longleftrightarrow> [] \<in> L"
      by (auto simp: nullable_iff KL Nullable_def Lang_def)
    fix a
    show "?R (Deriv a K) (Deriv a L)"
    proof cases
      assume "a \<in> set as"
      with rs Bisim'
      have "(Pderiv a R, Pderiv a S) \<in> set ps'"
        by (auto simp: is_Bisimulation_def)
      thus ?thesis by (fastforce simp: KL Deriv_Lang)
    next
      assume "a \<notin> set as"
      with Bisim' rs
      have "a \<notin> Atoms R \<union> Atoms S"
        by (fastforce simp: is_Bisimulation_def UN_subset_iff)
      then have "Pderiv a R = {}" "Pderiv a S = {}"
        by (metis Pderiv_no_occurrence Un_iff)+
      then have "Deriv a K = Lang {}" "Deriv a L = Lang {}" 
        unfolding KL Deriv_Lang by auto
      thus ?thesis by (auto simp: ps'_def)
    qed
  qed
qed


subsection {* Closure computation *}

fun test :: "'a Rexp_pairs * 'a Rexp_pairs \<Rightarrow> bool" where
"test (ws, ps) = (case ws of [] \<Rightarrow>  False | (R,S)#_ \<Rightarrow> Nullable R = Nullable S)"

fun step :: "'a list \<Rightarrow>
  'a Rexp_pairs * 'a Rexp_pairs \<Rightarrow> 'a Rexp_pairs * 'a Rexp_pairs"
where "step as (ws,ps) =
    (let
      (R,S) = hd ws;
      ps' = (R,S) # ps;
      succs = map (\<lambda>a. (Pderiv a R, Pderiv a S)) as;
      new = filter (\<lambda>p. p \<notin> set ps' \<union> set ws) succs
    in (new @ tl ws, ps'))"

definition closure ::
  "'a list \<Rightarrow> 'a Rexp_pairs * 'a Rexp_pairs
   \<Rightarrow> ('a Rexp_pairs * 'a Rexp_pairs) option" where
"closure as = while_option test (step as)"

definition pre_Bisim :: "'a list \<Rightarrow> 'a rexp set \<Rightarrow> 'a rexp set \<Rightarrow>
 'a Rexp_pairs * 'a Rexp_pairs \<Rightarrow> bool"
where
"pre_Bisim as R S = (\<lambda>(ws,ps).
 ((R,S) \<in> set ws \<union> set ps) \<and>
 (\<forall>(R,S)\<in> set ws \<union> set ps. Atoms R \<union> Atoms S \<subseteq> set as) \<and>
 (\<forall>(R,S)\<in> set ps. (Nullable R \<longleftrightarrow> Nullable S) \<and>
   (\<forall>a\<in>set as. (Pderiv a R, Pderiv a S) \<in> set ps \<union> set ws)))"

lemma step_set_eq: "\<lbrakk> test (ws,ps); step as (ws,ps) = (ws',ps') \<rbrakk>
  \<Longrightarrow> set ws' \<union> set ps' =
     set ws \<union> set ps
     \<union> (\<Union>a\<in>set as. {(Pderiv a (fst(hd ws)), Pderiv a (snd(hd ws)))})"
by(auto split: list.splits)

theorem closure_sound:
assumes result: "closure as ([(R,S)],[]) = Some([],ps)"
and atoms: "Atoms R \<union> Atoms S \<subseteq> set as"
shows "Lang R = Lang S"
proof-
  { fix st
    have "pre_Bisim as R S st \<Longrightarrow> test st \<Longrightarrow> pre_Bisim as R S (step as st)"
    unfolding pre_Bisim_def
    proof(split prod.splits, elim prod_caseE conjE, intro allI impI conjI)
      case goal1 thus ?case by(auto split: list.splits)
    next
      case (goal2 ws ps ws' ps')
      note goal2(2)[simp]
      from `test st` obtain wstl R S where [simp]: "ws = (R,S)#wstl"
        by (auto split: list.splits)
      from `step as st = (ws',ps')` obtain P where [simp]: "ps' = (R,S) # ps"
        and [simp]: "ws' = filter P (map (\<lambda>a. (Pderiv a R, Pderiv a S)) as) @ wstl"
        by auto
      have "\<forall>(R',S')\<in>set wstl \<union> set ps'. Atoms R' \<union> Atoms S' \<subseteq> set as"
        using goal2(4) by auto
      moreover
      have "\<forall>a\<in>set as. Atoms(Pderiv a R) \<union> Atoms(Pderiv a S) \<subseteq> set as"
        using goal2(4) by simp (metis (lifting) Atoms_Pderiv order_trans)
      ultimately show ?case by simp blast
    next
      case goal3 thus ?case
        by(clarsimp simp: image_iff split: prod.splits list.splits) metis
    qed
  }
  moreover
  from atoms
  have "pre_Bisim as R S ([(R,S)],[])" by (simp add: pre_Bisim_def)
  ultimately have pre_Bisim_ps: "pre_Bisim as R S ([],ps)"
    by (rule while_option_rule[OF _ result[unfolded closure_def]])
  then have "is_Bisimulation as ps" "(R,S) \<in> set ps"
    by (auto simp: pre_Bisim_def is_Bisimulation_def test_def)
  thus "Lang R = Lang S" by (rule Bisim_Lang_eq)
qed


subsection {* The overall procedure *}

definition check_eqv :: "'a rexp \<Rightarrow> 'a rexp \<Rightarrow> bool"
where
"check_eqv r s =
  (case closure (add_atoms r (add_atoms s [])) ([({r}, {s})], []) of
     Some([],_) \<Rightarrow> True | _ \<Rightarrow> False)"

lemma soundness: assumes "check_eqv r s" shows "lang r = lang s"
proof -
  let ?as = "add_atoms r (add_atoms s [])"
  obtain ps where 1: "closure ?as ([({r},{s})],[]) = Some([],ps)"
    using assms by (auto simp: check_eqv_def split:option.splits list.splits)
  then have "lang r = lang s"
    by(rule closure_sound[of _ "{r}" "{s}", simplified Lang_def, simplified])
      (auto simp: set_add_atoms Atoms_def)
  thus "lang r = lang s" by simp
qed

text{* Test: *}
lemma "check_eqv
  (Plus One (Times (Atom 0) (Star(Atom 0))))
  (Star(Atom(0::nat)))"
by eval

(* in progress

fun Pderivs :: "'a list \<Rightarrow> 'a rexp set \<Rightarrow> 'a rexp set" where
"Pderivs [] R = R" |
"Pderivs (a#as) R = Pderivs as (Pderiv a R)"

lemma finite_pderiv: "finite(pderiv a r)"
by(induction r) auto

lemma finite_Pderiv: "finite R \<Longrightarrow> finite(Pderiv a R)"
by(simp add:Pderiv_def finite_pderiv)

lemma assumes "ALL (R,S): set ws0 Un set bs0. finite R \<and> finite S"
 shows "EX p. closure as (ws0,bs0) = Some p"
unfolding closure_def
apply(rule wf_while_option_Some
  [where P = "%(ws,bs). ALL (R,S) : set ws Un set bs. finite R \<and> finite S"])
prefer 3 using assms apply simp
prefer 2 apply (fastforce simp: image_iff finite_Pderiv split: prod.splits list.splits)
term inv_image
term lex_prod
apply(rule wf_subset
  [where r = "inv_image (op \<subset>) (%(ws,bs). (UN (R,S):set ws0 Un set bs0.
                          UN xs. {(Pderivs xs R, Pderivs xs S)})
                         - set ws Un set bs)"]); <*lex*>
              (%(ws,bs). size ws)"])
*)

end
