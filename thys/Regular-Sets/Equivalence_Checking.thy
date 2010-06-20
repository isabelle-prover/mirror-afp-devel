header {* Deciding Regular Expression Equivalence *}

theory Equivalence_Checking
imports Regular_Exp While_Option
begin

text{* This theory is based on work by Jan Rutten \cite{Rutten98}. *}

subsection {* Term ordering *}

fun rexp_le :: "nat rexp \<Rightarrow> nat rexp \<Rightarrow> bool"
where
  "rexp_le Zero _ = True"
| "rexp_le _ Zero = False"
| "rexp_le One _ = True"
| "rexp_le _ One = False"
| "rexp_le (Atom i) (Atom j) = (i <= j)"
| "rexp_le (Atom _) _ = True"
| "rexp_le _ (Atom _) = False"
| "rexp_le (Star r) (Star s) = rexp_le r s"
| "rexp_le (Star _) _ = True"
| "rexp_le _ (Star _) = False"
| "rexp_le (Plus r r') (Plus s s') =
    (if r = s then rexp_le r' s' else rexp_le r s)"
| "rexp_le (Plus _ _) _ = True"
| "rexp_le _ (Plus _ _) = False"
| "rexp_le (Times r r') (Times s s') =
    (if r = s then rexp_le r' s' else rexp_le r s)"

subsection {* Normalizing operations *}

text {* associativity, commutativity, idempotence, zero *}

fun nPlus :: "nat rexp \<Rightarrow> nat rexp \<Rightarrow> nat rexp"
where
  "nPlus Zero r = r"
| "nPlus r Zero = r"
| "nPlus (Plus r s) t = nPlus r (nPlus s t)"
| "nPlus r (Plus s t) =
     (if r = s then (Plus s t)
     else if rexp_le r s then Plus r (Plus s t)
     else Plus s (nPlus r t))"
| "nPlus r s =
     (if r = s then r
      else if rexp_le r s then Plus r s
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
| "norm (Atom i) = Atom i"
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
| "ederiv i (Atom j) = (if i = j then One else Zero)"
| "ederiv i (Plus r s) = nPlus (ederiv i r) (ederiv i s)"
| "ederiv i (Times r s) =
    (let r's = nTimes (ederiv i r) s
     in if final r then nPlus r's (ederiv i s) else r's)"
| "ederiv i (Star r) = nTimes (ederiv i r) (Star r)"

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
  (\<forall>(r,s)\<in> set ps. (final r \<longleftrightarrow> final s) \<and>
    (\<forall>a\<in>set as. (ederiv a r, ederiv a s) \<in> set ps))"

lemma bisim_lang_eq:
assumes atoms: "\<forall>(r,s) \<in> set ps. atoms r \<union> atoms s \<subseteq> set as"
assumes bisim: "is_bisimulation as ps"
assumes "(r, s) \<in> set ps"
shows "lang r = lang s"
proof -
  def ps' \<equiv> "(Zero, Zero) # ps"
  with atoms bisim 
  have atoms': "\<forall>(r,s) \<in> set ps'. atoms r \<union> atoms s \<subseteq> set as"and bisim': "is_bisimulation as ps'"
    by (auto simp: is_bisimulation_def)
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
      with atoms' rs
      have "a \<notin> atoms r" "a \<notin> atoms s" by auto
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
      new = filter (\<lambda>p. p \<notin> set ps') (succs as (hd ws))
    in (new @ tl ws, ps'))"

definition closure ::
  "nat list \<Rightarrow> rexp_pairs * rexp_pairs
   \<Rightarrow> (rexp_pairs * rexp_pairs) option" where
"closure as = while test (step as)"

definition pre_bisim :: "nat list \<Rightarrow> rexp_pairs * rexp_pairs \<Rightarrow> bool"
where
"pre_bisim as = (\<lambda>(ws,ps).
 (\<forall>(r,s)\<in> set ps. (final r \<longleftrightarrow> final s) \<and>
   (\<forall>a\<in>set as. (ederiv a r, ederiv a s) \<in> set ps \<union> set ws)))"

lemma closure_sound_bisim:
assumes "closure as (ws,[]) = Some([],ps)"
shows "is_bisimulation as ps"
proof-
  { fix s have "pre_bisim as s \<Longrightarrow> test s \<Longrightarrow> pre_bisim as (step as s)"
      unfolding pre_bisim_def test_def step_def
      by (cases s) (auto simp: split_def split: list.splits) }
  moreover
  have "pre_bisim as (ws,[])" by (simp add: pre_bisim_def)
  ultimately have "pre_bisim as ([],ps)"
    by (rule while_rule[OF _ assms[unfolded closure_def]])
  thus "is_bisimulation as ps"
    by (simp add: pre_bisim_def is_bisimulation_def test_def)
qed

theorem closure_sound_subset:
assumes "closure as (ws,[]) = Some([],ps)"
shows "set ws \<subseteq> set ps"
proof-
  let ?I = "%s. set ws <= set(fst s @ snd s)"
  { fix s have "?I s \<Longrightarrow> test s \<Longrightarrow> ?I (step as s)"
      unfolding test_def step_def by (fastsimp split: list.splits) }
  moreover
  have "?I (ws,[])" by simp
  ultimately have "?I ([],ps)"
    by (rule while_rule[OF _ assms[unfolded closure_def]])

  thus "set ws <= set ps" by simp
qed

theorem closure_sound_atoms:
assumes "closure as (ws,[]) = Some([],ps)"
and "\<forall>(r,s) \<in> set ws. atoms r \<union> atoms s \<subseteq> set as"
shows "\<forall>(r,s) \<in> set ps. atoms r \<union> atoms s \<subseteq> set as"
proof-
  let ?I = "%s. \<forall>(r,s) \<in> set(fst s @ snd s). atoms r \<union> atoms s \<subseteq> set as"
  { fix s have "?I s \<Longrightarrow> test s \<Longrightarrow> ?I (step as s)"
      unfolding test_def step_def
      by (fastsimp split: list.splits dest!: subsetD[OF atoms_ederiv]) }
  moreover
  have "?I (ws,[])" using assms(2) by simp
  ultimately have "?I ([],ps)"
    by (rule while_rule[of ?I, OF _ assms(1)[unfolded closure_def]]) simp
  thus ?thesis by simp
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
  have "lang (norm r) = lang (norm s)"
  proof (rule bisim_lang_eq[OF _ closure_sound_bisim[OF 1]])
    show "\<forall>(r, s)\<in>set ps. atoms r \<union> atoms s \<subseteq> set ?as"
      using closure_sound_atoms[OF 1]
      by (fastsimp simp: set_add_atoms dest!: subsetD[OF atoms_norm])
    show "(norm r, norm s) \<in> set ps" using closure_sound_subset[OF 1] by simp
  qed
  thus "lang r = lang s" by simp
qed

lemma "check_eqv (Plus One (Times (Atom 0) (Star(Atom 0)))) (Star(Atom 0))"
by eval

end