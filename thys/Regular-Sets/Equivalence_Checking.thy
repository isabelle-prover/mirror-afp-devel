header {* Deciding Regular Expression Equivalence *}

theory Equivalence_Checking
imports Regular_Exp While_Combinator
begin

text{* This theory is based on work by Jan Rutten \cite{Rutten98}. *}

subsection {* Term ordering *}

fun le_rexp :: "nat rexp \<Rightarrow> nat rexp \<Rightarrow> bool"
where
  "le_rexp Zero _ = True"
| "le_rexp _ Zero = False"
| "le_rexp One _ = True"
| "le_rexp _ One = False"
| "le_rexp (Atom a) (Atom b) = (a <= b)"
| "le_rexp (Atom _) _ = True"
| "le_rexp _ (Atom _) = False"
| "le_rexp (Star r) (Star s) = le_rexp r s"
| "le_rexp (Star _) _ = True"
| "le_rexp _ (Star _) = False"
| "le_rexp (Plus r r') (Plus s s') =
    (if r = s then le_rexp r' s' else le_rexp r s)"
| "le_rexp (Plus _ _) _ = True"
| "le_rexp _ (Plus _ _) = False"
| "le_rexp (Times r r') (Times s s') =
    (if r = s then le_rexp r' s' else le_rexp r s)"

subsection {* Normalizing operations *}

text {* associativity, commutativity, idempotence, zero *}

fun nPlus :: "nat rexp \<Rightarrow> nat rexp \<Rightarrow> nat rexp"
where
  "nPlus Zero r = r"
| "nPlus r Zero = r"
| "nPlus (Plus r s) t = nPlus r (nPlus s t)"
| "nPlus r (Plus s t) =
     (if r = s then (Plus s t)
     else if le_rexp r s then Plus r (Plus s t)
     else Plus s (nPlus r t))"
| "nPlus r s =
     (if r = s then r
      else if le_rexp r s then Plus r s
      else Plus s r)"

lemma lang_nPlus[simp]: "lang (nPlus r s) = lang (Plus r s)"
by (induct r s rule: nPlus.induct) auto

text {* associativity, zero, one *}

fun nTimes :: "nat rexp \<Rightarrow> nat rexp \<Rightarrow> nat rexp"
where
  "nTimes Zero _ = Zero"
| "nTimes _ Zero = Zero"
| "nTimes One r = r"
| "nTimes r One = r"
| "nTimes (Times r s) t = Times r (nTimes s t)"
| "nTimes r s = Times r s"

lemma lang_nTimes[simp]: "lang (nTimes r s) = lang (Times r s)"
by (induct r s rule: nTimes.induct) (auto simp: conc_assoc)

primrec norm :: "nat rexp \<Rightarrow> nat rexp"
where
  "norm Zero = Zero"
| "norm One = One"
| "norm (Atom a) = Atom a"
| "norm (Plus r s) = nPlus (norm r) (norm s)"
| "norm (Times r s) = nTimes (norm r) (norm s)"
| "norm (Star r) = Star (norm r)"

lemma lang_norm[simp]: "lang (norm r) = lang r"
by (induct r) auto


subsection {* Finality and Derivative *}

primrec final :: "'a rexp \<Rightarrow> bool"
where
  "final Zero = False"
| "final One = True"
| "final (Atom _) = False"
| "final (Plus r s) = (final r \<or> final s)"
| "final (Times r s) = (final r \<and> final s)"
| "final (Star _) = True"

lemma lang_final: "final r = ([] \<in> lang r)"
by (induct r) (auto simp: conc_def)

primrec ederiv :: "nat \<Rightarrow> nat rexp \<Rightarrow> nat rexp"
where
  "ederiv _ Zero = Zero"
| "ederiv _ One = Zero"
| "ederiv a (Atom b) = (if a = b then One else Zero)"
| "ederiv a (Plus r s) = nPlus (ederiv a r) (ederiv a s)"
| "ederiv a (Times r s) =
    (let r's = nTimes (ederiv a r) s
     in if final r then nPlus r's (ederiv a s) else r's)"
| "ederiv a (Star r) = nTimes (ederiv a r) (Star r)"

lemma lang_ederiv: "lang (ederiv a r) = deriv a (lang r)"
by (induct r) (auto simp: Let_def deriv_conc1 deriv_conc2 lang_final)

lemma deriv_no_occurrence: 
  "x \<notin> atoms r \<Longrightarrow> ederiv x r = Zero"
by (induct r) auto

lemma atoms_nPlus[simp]: "atoms (nPlus r s) = atoms r \<union> atoms s"
by (induct r s rule: nPlus.induct) auto

lemma atoms_nTimes: "atoms (nTimes r s) \<subseteq> atoms r \<union> atoms s"
by (induct r s rule: nTimes.induct) auto

lemma atoms_norm: "atoms (norm r) \<subseteq> atoms r"
by (induct r) (auto dest!:subsetD[OF atoms_nTimes])

lemma atoms_ederiv: "atoms (ederiv a r) \<subseteq> atoms r"
by (induct r) (auto simp: Let_def dest!:subsetD[OF atoms_nTimes])


subsection {* Bisimulation between regular expressions *}

types rexp_pair = "nat rexp * nat rexp"
types rexp_pairs = "rexp_pair list"

definition is_bisimulation :: 
  "nat list \<Rightarrow> rexp_pairs \<Rightarrow> bool"
where
"is_bisimulation as ps =
  (\<forall>(r,s)\<in> set ps. (atoms r \<union> atoms s \<subseteq> set as) \<and> (final r \<longleftrightarrow> final s) \<and>
    (\<forall>a\<in>set as. (ederiv a r, ederiv a s) \<in> set ps))"

lemma bisim_lang_eq:
assumes bisim: "is_bisimulation as ps"
assumes "(r, s) \<in> set ps"
shows "lang r = lang s"
proof -
  def ps' \<equiv> "(Zero, Zero) # ps"
  from bisim have bisim': "is_bisimulation as ps'"
    by (auto simp: ps'_def is_bisimulation_def)

  let ?R = "\<lambda>K L. (\<exists>(r,s)\<in>set ps'. K = lang r \<and> L = lang s)"
  show ?thesis
  proof (rule language_coinduct[where R="?R"])
    from `(r, s) \<in> set ps` 
    have "(r, s) \<in> set ps'" by (auto simp: ps'_def)
    thus "?R (lang r) (lang s)" by auto
  next
    fix K L assume "?R K L"
    then obtain r s where rs: "(r, s) \<in> set ps'"
      and KL: "K = lang r" "L = lang s" by auto
    with bisim' have "final r \<longleftrightarrow> final s"
      by (auto simp: is_bisimulation_def)
    thus "[] \<in> K \<longleftrightarrow> [] \<in> L" by (auto simp: lang_final KL)
    fix a
    show "?R (deriv a K) (deriv a L)"
    proof cases
      assume "a \<in> set as"
      with rs bisim'
      have "(ederiv a r, ederiv a s) \<in> set ps'"
        by (auto simp: is_bisimulation_def)
      thus ?thesis by (force simp: KL lang_ederiv)
    next
      assume "a \<notin> set as"
      with bisim' rs
      have "a \<notin> atoms r" "a \<notin> atoms s" by (auto simp: is_bisimulation_def)
      then have "ederiv a r = Zero" "ederiv a s = Zero"
        by (auto intro: deriv_no_occurrence)
      then have "deriv a K = lang Zero" 
        "deriv a L = lang Zero" 
        unfolding KL lang_ederiv[symmetric] by auto
      thus ?thesis by (auto simp: ps'_def)
    qed
  qed  
qed

subsection {* Closure computation *}

fun succs :: "nat list \<Rightarrow> rexp_pair \<Rightarrow> rexp_pairs" where
"succs as (r, s) = map (\<lambda>a. (ederiv a r, ederiv a s)) as"

definition test :: "rexp_pairs * rexp_pairs \<Rightarrow> bool"
where "test = (\<lambda>([],_) \<Rightarrow> False | ((p,q)#_, _) \<Rightarrow> final p = final q)"

definition step :: "nat list \<Rightarrow> rexp_pairs * rexp_pairs \<Rightarrow> rexp_pairs * rexp_pairs"
where "step as = (\<lambda>(ws,ps).
    let 
      ps' = hd ws # ps;
      new = filter (\<lambda>p. p \<notin> set ps' \<union> set ws) (succs as (hd ws))
    in (new @ tl ws, ps'))"

definition closure ::
  "nat list \<Rightarrow> rexp_pairs * rexp_pairs
   \<Rightarrow> (rexp_pairs * rexp_pairs) option" where
"closure as = while_option test (step as)"

definition pre_bisim :: "nat list \<Rightarrow> nat rexp \<Rightarrow> nat rexp \<Rightarrow>
 rexp_pairs * rexp_pairs \<Rightarrow> bool"
where
"pre_bisim as r s = (\<lambda>(ws,ps).
 ((r, s) \<in> set ws \<union> set ps) \<and>
 (\<forall>(r,s)\<in> set ws \<union> set ps. atoms r \<union> atoms s \<subseteq> set as) \<and>
 (\<forall>(r,s)\<in> set ps. (final r \<longleftrightarrow> final s) \<and>
   (\<forall>a\<in>set as. (ederiv a r, ederiv a s) \<in> set ps \<union> set ws)))"

theorem closure_sound:
assumes result: "closure as ([(r,s)],[]) = Some([],ps)"
and atoms: "atoms r \<union> atoms s \<subseteq> set as"
shows "lang r = lang s"
proof-
  { fix st have "pre_bisim as r s st \<Longrightarrow> test st \<Longrightarrow> pre_bisim as r s (step as st)"
      unfolding pre_bisim_def test_def step_def
      by (cases st) (auto simp: split_def split: list.splits
        dest!: subsetD[OF atoms_ederiv]) }
  moreover
  from atoms
  have "pre_bisim as r s ([(r,s)],[])" by (simp add: pre_bisim_def)
  ultimately have pre_bisim_ps: "pre_bisim as r s ([],ps)"
    by (rule while_option_rule[OF _ result[unfolded closure_def]])
  then have "is_bisimulation as ps" "(r, s) \<in> set ps"
    by (auto simp: pre_bisim_def is_bisimulation_def test_def)
  thus "lang r = lang s" by (rule bisim_lang_eq)
qed


subsection {* The overall procedure *}

primrec add_atoms :: "nat rexp \<Rightarrow> nat list \<Rightarrow> nat list"
where
  "add_atoms Zero = id"
| "add_atoms One = id"
| "add_atoms (Atom a) = List.insert a"
| "add_atoms (Plus r s) = add_atoms s o add_atoms r"
| "add_atoms (Times r s) = add_atoms s o add_atoms r"
| "add_atoms (Star r) = add_atoms r"

lemma set_add_atoms: "set (add_atoms r as) = atoms r \<union> set as"
by (induct r arbitrary: as) auto

definition check_eqv :: "nat rexp \<Rightarrow> nat rexp \<Rightarrow> bool"
where
"check_eqv r s =
  (case closure (add_atoms r (add_atoms s [])) ([(norm r, norm s)], []) of
     Some([],_) \<Rightarrow> True | _ \<Rightarrow> False)"

lemma soundness: 
assumes "check_eqv r s" shows "lang r = lang s"
proof -
  let ?as = "add_atoms r (add_atoms s [])"
  obtain ps where 1: "closure ?as ([(norm r,norm s)],[]) = Some([],ps)"
    using assms by (auto simp: check_eqv_def split:option.splits list.splits)
  then have "lang (norm r) = lang (norm s)"
    by (rule closure_sound) (auto simp: set_add_atoms dest!: subsetD[OF atoms_norm])
  thus "lang r = lang s" by simp
qed

lemma "check_eqv (Plus One (Times (Atom 0) (Star(Atom 0)))) (Star(Atom 0))"
by eval

end