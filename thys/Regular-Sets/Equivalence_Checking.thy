header {* Deciding Regular Expression Equivalence *}

theory Equivalence_Checking
imports
  Regular_Exp
  "~~/src/HOL/Library/While_Combinator"
begin

subsection {* Normalizing operations *}

text {* associativity, commutativity, idempotence, zero *}

fun nPlus :: "'a::order rexp \<Rightarrow> 'a rexp \<Rightarrow> 'a rexp"
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
by (induction r s rule: nPlus.induct) auto

text {* associativity, zero, one *}

fun nTimes :: "'a::order rexp \<Rightarrow> 'a rexp \<Rightarrow> 'a rexp"
where
  "nTimes Zero _ = Zero"
| "nTimes _ Zero = Zero"
| "nTimes One r = r"
| "nTimes r One = r"
| "nTimes (Times r s) t = Times r (nTimes s t)"
| "nTimes r s = Times r s"

lemma lang_nTimes[simp]: "lang (nTimes r s) = lang (Times r s)"
by (induction r s rule: nTimes.induct) (auto simp: conc_assoc)

primrec norm :: "'a::order rexp \<Rightarrow> 'a rexp"
where
  "norm Zero = Zero"
| "norm One = One"
| "norm (Atom a) = Atom a"
| "norm (Plus r s) = nPlus (norm r) (norm s)"
| "norm (Times r s) = nTimes (norm r) (norm s)"
| "norm (Star r) = Star (norm r)"

lemma lang_norm[simp]: "lang (norm r) = lang r"
by (induct r) auto


subsection {* Normalizing Derivative *}

primrec nderiv :: "'a::order \<Rightarrow> 'a rexp \<Rightarrow> 'a rexp"
where
  "nderiv _ Zero = Zero"
| "nderiv _ One = Zero"
| "nderiv a (Atom b) = (if a = b then One else Zero)"
| "nderiv a (Plus r s) = nPlus (nderiv a r) (nderiv a s)"
| "nderiv a (Times r s) =
    (let r's = nTimes (nderiv a r) s
     in if nullable r then nPlus r's (nderiv a s) else r's)"
| "nderiv a (Star r) = nTimes (nderiv a r) (Star r)"

lemma lang_nderiv: "lang (nderiv a r) = Deriv a (lang r)"
by (induction r) (auto simp: Let_def nullable_iff)

lemma deriv_no_occurrence: 
  "x \<notin> atoms r \<Longrightarrow> nderiv x r = Zero"
by (induction r) auto

lemma atoms_nPlus[simp]: "atoms (nPlus r s) = atoms r \<union> atoms s"
by (induction r s rule: nPlus.induct) auto

lemma atoms_nTimes: "atoms (nTimes r s) \<subseteq> atoms r \<union> atoms s"
by (induction r s rule: nTimes.induct) auto

lemma atoms_norm: "atoms (norm r) \<subseteq> atoms r"
by (induction r) (auto dest!:subsetD[OF atoms_nTimes])

lemma atoms_nderiv: "atoms (nderiv a r) \<subseteq> atoms r"
by (induction r) (auto simp: Let_def dest!:subsetD[OF atoms_nTimes])


subsection {* Bisimulation between languages and regular expressions *}

coinductive bisimilar :: "'a lang \<Rightarrow> 'a lang \<Rightarrow> bool" where
"([] \<in> K \<longleftrightarrow> [] \<in> L) 
 \<Longrightarrow> (\<And>x. bisimilar (Deriv x K) (Deriv x L))
 \<Longrightarrow> bisimilar K L"

lemma equal_if_bisimilar:
assumes "bisimilar K L" shows "K = L"
proof (rule set_eqI)
  fix w
  from `bisimilar K L` show "w \<in> K \<longleftrightarrow> w \<in> L"
  proof (induct w arbitrary: K L)
    case Nil thus ?case by (auto elim: bisimilar.cases)
  next
    case (Cons a w K L)
    from `bisimilar K L` have "bisimilar (Deriv a K) (Deriv a L)"
      by (auto elim: bisimilar.cases)
    then have "w \<in> Deriv a K \<longleftrightarrow> w \<in> Deriv a L" by (rule Cons(1))
    thus ?case by (auto simp: Deriv_def)
  qed
qed

lemma language_coinduct:
fixes R (infixl "\<sim>" 50)
assumes "K \<sim> L"
assumes "\<And>K L. K \<sim> L \<Longrightarrow> ([] \<in> K \<longleftrightarrow> [] \<in> L)"
assumes "\<And>K L x. K \<sim> L \<Longrightarrow> Deriv x K \<sim> Deriv x L"
shows "K = L"
apply (rule equal_if_bisimilar)
apply (rule bisimilar.coinduct[of R, OF `K \<sim> L`])
apply (auto simp: assms)
done

type_synonym 'a rexp_pair = "'a rexp * 'a rexp"
type_synonym 'a rexp_pairs = "'a rexp_pair list"

definition is_bisimulation ::  "'a::order list \<Rightarrow> 'a rexp_pair set \<Rightarrow> bool"
where
"is_bisimulation as R =
  (\<forall>(r,s)\<in> R. (atoms r \<union> atoms s \<subseteq> set as) \<and> (nullable r \<longleftrightarrow> nullable s) \<and>
    (\<forall>a\<in>set as. (nderiv a r, nderiv a s) \<in> R))"

lemma bisim_lang_eq:
assumes bisim: "is_bisimulation as ps"
assumes "(r, s) \<in> ps"
shows "lang r = lang s"
proof -
  def ps' \<equiv> "insert (Zero, Zero) ps"
  from bisim have bisim': "is_bisimulation as ps'"
    by (auto simp: ps'_def is_bisimulation_def)
  let ?R = "\<lambda>K L. (\<exists>(r,s)\<in>ps'. K = lang r \<and> L = lang s)"
  show ?thesis
  proof (rule language_coinduct[where R="?R"])
    from `(r, s) \<in> ps` 
    have "(r, s) \<in> ps'" by (auto simp: ps'_def)
    thus "?R (lang r) (lang s)" by auto
  next
    fix K L assume "?R K L"
    then obtain r s where rs: "(r, s) \<in> ps'"
      and KL: "K = lang r" "L = lang s" by auto
    with bisim' have "nullable r \<longleftrightarrow> nullable s"
      by (auto simp: is_bisimulation_def)
    thus "[] \<in> K \<longleftrightarrow> [] \<in> L" by (auto simp: nullable_iff KL)
    fix a
    show "?R (Deriv a K) (Deriv a L)"
    proof cases
      assume "a \<in> set as"
      with rs bisim'
      have "(nderiv a r, nderiv a s) \<in> ps'"
        by (auto simp: is_bisimulation_def)
      thus ?thesis by (force simp: KL lang_nderiv)
    next
      assume "a \<notin> set as"
      with bisim' rs
      have "a \<notin> atoms r" "a \<notin> atoms s" by (auto simp: is_bisimulation_def)
      then have "nderiv a r = Zero" "nderiv a s = Zero"
        by (auto intro: deriv_no_occurrence)
      then have "Deriv a K = lang Zero" 
        "Deriv a L = lang Zero" 
        unfolding KL lang_nderiv[symmetric] by auto
      thus ?thesis by (auto simp: ps'_def)
    qed
  qed  
qed

subsection {* Closure computation *}

definition closure ::
  "'a::order list \<Rightarrow> 'a rexp_pair \<Rightarrow> ('a rexp_pairs * 'a rexp_pair set) option"
where
"closure as = rtrancl_while (%(r,s). nullable r = nullable s)
  (%(r,s). map (\<lambda>a. (nderiv a r, nderiv a s)) as)"

definition pre_bisim :: "'a::order list \<Rightarrow> 'a rexp \<Rightarrow> 'a rexp \<Rightarrow>
 'a rexp_pairs * 'a rexp_pair set \<Rightarrow> bool"
where
"pre_bisim as r s = (\<lambda>(ws,R).
 (r,s) \<in> R \<and> set ws \<subseteq> R \<and>
 (\<forall>(r,s)\<in> R. atoms r \<union> atoms s \<subseteq> set as) \<and>
 (\<forall>(r,s)\<in> R - set ws. (nullable r \<longleftrightarrow> nullable s) \<and>
   (\<forall>a\<in>set as. (nderiv a r, nderiv a s) \<in> R)))"

theorem closure_sound:
assumes result: "closure as (r,s) = Some([],R)"
and atoms: "atoms r \<union> atoms s \<subseteq> set as"
shows "lang r = lang s"
proof-
  let ?test = "%(ws,_). ws \<noteq> [] \<and> (%(r,s). nullable r = nullable s)(hd ws)"
  let ?step = "(%(ws,R).
     let x = hd ws; new = filter (\<lambda>y. y \<notin> R) ((\<lambda>(r,s). map (\<lambda>a. (nderiv a r, nderiv a s)) as) x)
     in (new @ tl ws, set new \<union> R))"
  { fix st have "pre_bisim as r s st \<Longrightarrow> ?test st \<Longrightarrow> pre_bisim as r s (?step st)"
      unfolding pre_bisim_def
      by (cases st, auto simp: Let_def neq_Nil_conv Ball_def split_def split: list.splits prod.splits
        dest!: subsetD[OF atoms_nderiv], blast+)
 }
  moreover
  from atoms
  have "pre_bisim as r s ([(r,s)],{(r,s)})" by (simp add: pre_bisim_def)
  ultimately have pre_bisim_ps: "pre_bisim as r s ([],R)"
    by (rule while_option_rule[OF _ result[unfolded closure_def rtrancl_while_def]])
  then have "is_bisimulation as R" "(r, s) \<in> R"
    by (auto simp: pre_bisim_def is_bisimulation_def)
  thus "lang r = lang s" by (rule bisim_lang_eq)
qed

subsection {* Bisimulation-free proof of closure computation *}

text{* The equivalence check can be viewed as the product construction
of two automata. The state space is the reflexive transitive closure of
the pair of next-state functions, i.e. derivatives. *}

lemma rtrancl_nderiv_nderivs: defines "nderivs == foldl (%r a. nderiv a r)"
shows "{((r,s),(nderiv a r,nderiv a s))| r s a. a : A}^* =
       {((r,s),(nderivs r w,nderivs s w))| r s w. w : lists A}" (is "?L = ?R")
proof-
  note [simp] = nderivs_def
  { fix r s r' s'
    have "((r,s),(r',s')) : ?L \<Longrightarrow> ((r,s),(r',s')) : ?R"
    proof(induction rule: converse_rtrancl_induct2)
      case refl show ?case by (force intro!: foldl.simps(1)[symmetric])
    next
      case step thus ?case by(force intro!: foldl.simps(2)[symmetric])
    qed
  } moreover
  { fix r s r' s'
    { fix w have "\<forall>x\<in>set w. x \<in> A \<Longrightarrow> ((r, s), nderivs r w, nderivs s w) :?L"
      proof(induction w rule: rev_induct)
        case Nil show ?case by simp
      next
        case snoc thus ?case by (auto elim!: rtrancl_into_rtrancl)
      qed
    } 
    hence "((r,s),(r',s')) : ?R \<Longrightarrow> ((r,s),(r',s')) : ?L" by auto
  } ultimately show ?thesis by (auto simp: in_lists_conv_set) blast
qed

lemma nullable_nderivs:
  "nullable (foldl (%r a. nderiv a r) r w) = (w : lang r)"
by (induct w arbitrary: r) (simp_all add: nullable_iff lang_nderiv Deriv_def)

theorem closure_sound_complete:
assumes result: "closure as (r,s) = Some(ws,R)"
and atoms: "set as = atoms r \<union> atoms s"
shows "ws = [] \<longleftrightarrow> lang r = lang s"
proof -
  have leq: "(lang r = lang s) =
  (\<forall>(r',s') \<in> {((r0,s0),(nderiv a r0,nderiv a s0))| r0 s0 a. a : set as}^* `` {(r,s)}.
    nullable r' = nullable s')"
    by(simp add: atoms rtrancl_nderiv_nderivs Ball_def lang_eq_ext imp_ex nullable_nderivs
         del:Un_iff)
  have "{(x,y). y \<in> set ((\<lambda>(p,q). map (\<lambda>a. (nderiv a p, nderiv a q)) as) x)} =
    {((r,s), nderiv a r, nderiv a s) |r s a. a \<in> set as}"
    by auto
  with atoms rtrancl_while_Some[OF result[unfolded closure_def]]
  show ?thesis by (auto simp add: leq Ball_def split: if_splits)
qed

subsection {* The overall procedure *}

primrec add_atoms :: "'a rexp \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "add_atoms Zero = id"
| "add_atoms One = id"
| "add_atoms (Atom a) = List.insert a"
| "add_atoms (Plus r s) = add_atoms s o add_atoms r"
| "add_atoms (Times r s) = add_atoms s o add_atoms r"
| "add_atoms (Star r) = add_atoms r"

lemma set_add_atoms: "set (add_atoms r as) = atoms r \<union> set as"
by (induct r arbitrary: as) auto


definition check_eqv :: "nat rexp \<Rightarrow> nat rexp \<Rightarrow> bool" where
"check_eqv r s =
  (let nr = norm r; ns = norm s; as = add_atoms nr (add_atoms ns [])
   in case closure as (nr, ns) of
     Some([],_) \<Rightarrow> True | _ \<Rightarrow> False)"

lemma soundness: 
assumes "check_eqv r s" shows "lang r = lang s"
proof -
  let ?nr = "norm r" let ?ns = "norm s"
  let ?as = "add_atoms ?nr (add_atoms ?ns [])"
  obtain R where 1: "closure ?as (?nr,?ns) = Some([],R)"
    using assms by (auto simp: check_eqv_def Let_def split:option.splits list.splits)
  then have "lang (norm r) = lang (norm s)"
    by (rule closure_sound) (auto simp: set_add_atoms dest!: subsetD[OF atoms_norm])
  thus "lang r = lang s" by simp
qed

text{* Test: *}
lemma "check_eqv (Plus One (Times (Atom 0) (Star(Atom 0)))) (Star(Atom 0))"
by eval

end
