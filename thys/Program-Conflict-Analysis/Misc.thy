(*  Title:       Miscellanneous Definitions and Lemmas
    Author:      Peter Lammich <peter.lammich@uni-muenster.de>
    Maintainer:  Peter Lammich <peter.lammich@uni-muenster.de>
*)

section {* Miscellanneous Definitions and Lemmas *}

theory Misc
imports Main "~~/src/HOL/Library/Multiset" "~~/src/HOL/Library/Sublist_Order"
begin
text_raw {*\label{thy:Misc}*}

text {* Here we provide a collection of miscellaneous definitions and helper lemmas *}

subsection "Miscellanneous (1)"
text {* This stuff is used in this theory itself, and thus occurs in first place. There is another ,,Miscellaneous''-section at the end of this theory *}
subsubsection "AC-operators"
  
text {* Locale to declare AC-laws as simplification rules *}
locale AC =
  fixes f
  assumes commute[simp]: "f x y = f y x"
  assumes assoc[simp]: "f (f x y) z = f x (f y z)"

lemma (in AC) left_commute[simp]: "f x (f y z) = f y (f x z)"
  by (simp only: assoc[symmetric]) simp

text {* Locale to define functions from surjective, unique relations *}
locale su_rel_fun =
  fixes F and f
  assumes unique: "\<lbrakk>(A,B)\<in>F; (A,B')\<in>F\<rbrakk> \<Longrightarrow> B=B'"
  assumes surjective: "\<lbrakk>!!B. (A,B)\<in>F \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  assumes f_def: "f A == THE B. (A,B)\<in>F"

lemma (in su_rel_fun) repr1: "(A,f A)\<in>F" proof (unfold f_def)
  obtain B where "(A,B)\<in>F" by (rule surjective)
  with theI[where P="\<lambda>B. (A,B)\<in>F", OF this] show "(A, THE x. (A, x) \<in> F) \<in> F" by (blast intro: unique)
qed
  
lemma (in su_rel_fun) repr2: "(A,B)\<in>F \<Longrightarrow> B=f A" using repr1
  by (blast intro: unique)

lemma (in su_rel_fun) repr: "(f A = B) = ((A,B)\<in>F)" using repr1 repr2
  by (blast) 


subsection {* Abbreviations for list order *}

abbreviation ileq :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"  (infix "\<preceq>" 50) where
  "op \<preceq> \<equiv> op \<le>"

abbreviation ilt :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"  (infix "\<prec>" 50) where
  "op \<prec> \<equiv> op <"


subsection {* Sets *}
  lemma setsum_subset_split: assumes P: "finite A" "B\<subseteq>A" shows T: "setsum f A = setsum f (A-B) + setsum f B" proof -
    from P have 1: "A = (A-B) \<union> B" by auto
    have 2: "(A-B) \<inter> B = {}" by auto
    from P have 3: "finite B" by (simp add: finite_subset)
    from P have 4: "finite (A-B)" by simp
    from 2 3 4 setsum.union_disjoint have "setsum f ((A-B) \<union> B) = setsum f (A-B) + setsum f B" by blast
    with 1 show ?thesis by simp
  qed


subsection {* Multisets *}

(*
  The following is a syntax extension for multisets. Unfortunately, it depends on a change in the Library/Multiset.thy, so it is commented out here, until it will be incorporated 
  into Library/Multiset.thy by its maintainers.

  The required change in Library/Multiset.thy is removing the syntax for single:
     - single :: "'a => 'a multiset"    ("{#_#}")
     + single :: "'a => 'a multiset"

  And adding the following translations instead:
  
     + syntax
     + "_multiset" :: "args \<Rightarrow> 'a multiset" ("{#(_)#}")

     + translations
     +   "{#x, xs#}" == "{#x#} + {#xs#}" 
     +   "{# x #}" == "single x"

  This translates "{# \<dots> #}" into a sum of singletons, that is parenthesized to the right. ?? Can we also achieve left-parenthesizing ??

*)


  (* Let's try what happens if declaring AC-rules for multiset union as simp-rules *)
(*declare union_ac[simp] -- don't do it !*)

subsubsection {* Case distinction *}

lemma multiset_induct'[case_names empty add]: "\<lbrakk>P {#}; \<And>M x. P M \<Longrightarrow> P ({#x#}+M)\<rbrakk> \<Longrightarrow> P M"
  by (induct rule: multiset_induct) (auto simp add: union_commute)

subsubsection {* Count *}
  lemma count_ne_remove: "\<lbrakk> x ~= t\<rbrakk> \<Longrightarrow> count S x = count (S-{#t#}) x"
    by (auto)
  lemma mset_empty_count[simp]: "(\<forall>p. count M p = 0) = (M={#})"
    by (auto simp add: multiset_eq_iff)

subsubsection {* Union, difference and intersection *}

  lemma size_diff_se: "\<lbrakk>t :# S\<rbrakk> \<Longrightarrow> size S = size (S - {#t#}) + 1" proof (unfold size_multiset_overloaded_eq)
    let ?SIZE = "setsum (count S) (set_mset S)"
    assume A: "t :# S"
    from A have SPLITPRE: "finite (set_mset S) & {t}\<subseteq>(set_mset S)" by auto
    hence "?SIZE = setsum (count S) (set_mset S - {t}) + setsum (count S) {t}" by (blast dest: setsum_subset_split)
    hence "?SIZE = setsum (count S) (set_mset S - {t}) + count (S) t" by auto
    moreover with A have "count S t = count (S-{#t#}) t + 1" by auto
    ultimately have D: "?SIZE = setsum (count S) (set_mset S - {t}) + count (S-{#t#}) t + 1" by (arith)
    moreover have "setsum (count S) (set_mset S - {t}) = setsum (count (S-{#t#})) (set_mset S - {t})" proof -
      have "ALL x:(set_mset S - {t}) . count S x = count (S-{#t#}) x" by (auto iff add: count_ne_remove)
      thus ?thesis by simp
    qed
    ultimately have D: "?SIZE = setsum (count (S-{#t#})) (set_mset S - {t}) + count (S-{#t#}) t + 1" by (simp)
    moreover
    { assume CASE: "count (S-{#t#}) t = 0"
      from CASE have "set_mset S - {t} = set_mset (S-{#t#})" by (auto iff add: set_mset_def)
      with CASE D have "?SIZE = setsum (count (S-{#t#})) (set_mset (S - {#t#})) + 1" by simp
    }
    moreover
    { assume CASE: "count (S-{#t#}) t ~= 0"
      from CASE have 1: "set_mset S = set_mset (S-{#t#})" by (auto iff add: set_mset_def)
      moreover from D have "?SIZE = setsum (count (S-{#t#})) (set_mset S - {t}) + setsum (count (S-{#t#})) {t} + 1" by simp
      moreover from SPLITPRE setsum_subset_split have "setsum (count (S-{#t#})) (set_mset S) = setsum (count (S-{#t#})) (set_mset S - {t}) + setsum (count (S-{#t#})) {t}" by (blast)
      ultimately have "?SIZE = setsum (count (S-{#t#})) (set_mset (S-{#t#})) + 1" by simp
    }
    ultimately show "?SIZE = setsum (count (S-{#t#})) (set_mset (S - {#t#})) + 1" by blast
  qed

  (* TODO: Check whether this proof can be done simpler *)
  lemma mset_union_diff_comm: "t :# S \<Longrightarrow> T + (S - {#t#}) = (T + S) - {#t#}" proof -
    assume "t :# S"
    hence "count S t = count (S-{#t#}) t + 1" by auto
    hence "count (S+T) t = count (S-{#t#}+T) t + 1" by auto
    hence "count (S+T-{#t#}) t = count (S-{#t#}+T) t" by (simp)
    moreover have "ALL x. x~=t \<longrightarrow> count (S+T-{#t#}) x = count (S-{#t#}+T) x" by auto
    ultimately show ?thesis by (auto simp add: union_ac iff add: multiset_eq_iff)
  qed

  lemma mset_right_cancel_union: "\<lbrakk>a :# A+B; ~(a :# B)\<rbrakk> \<Longrightarrow> a:#A"
    by (simp)
  lemma mset_left_cancel_union: "\<lbrakk>a :# A+B; ~(a :# A)\<rbrakk> \<Longrightarrow> a:#B"
    by (simp)
  
  lemmas mset_cancel_union = mset_right_cancel_union mset_left_cancel_union

  lemma mset_right_cancel_elem: "\<lbrakk>a :# A+{#b#}; a~=b\<rbrakk> \<Longrightarrow> a:#A"
    apply(subgoal_tac "~(a :# {#b#})")
    apply(auto)
  done

  lemma mset_left_cancel_elem: "\<lbrakk>a :# {#b#}+A; a~=b\<rbrakk> \<Longrightarrow> a:#A"
    apply(subgoal_tac "~(a :# {#b#})")
    apply(auto)
  done

  lemmas mset_cancel_elem = mset_right_cancel_elem mset_left_cancel_elem

  lemma mset_diff_cancel1elem[simp]: "~(a :# B) \<Longrightarrow> {#a#}-B = {#a#}" proof -
    assume A: "~(a :# B)"
    hence "count ({#a#}-B) a = count ({#a#}) a" by auto
    moreover have "ALL e . e~=a \<longrightarrow> count ({#a#}-B) e = count ({#a#}) e" by auto
    ultimately show ?thesis by (auto simp add: multiset_eq_iff)
  qed

  (*lemma union_diff_assoc_se: "t :# B \<Longrightarrow> (A+B)-{#t#} = A + (B-{#t#})"
    by (auto iff add: multiset_eq_iff)
  lemma union_diff_assoc_se2: "t :# A \<Longrightarrow> (A+B)-{#t#} = (A-{#t#}) + B"
    by (auto iff add: multiset_eq_iff)
  lemmas union_diff_assoc_se = union_diff_assoc_se1 union_diff_assoc_se2*)

  lemma union_diff_assoc: "C-B={#} \<Longrightarrow> (A+B)-C = A + (B-C)"
    by (simp add: multiset_eq_iff)

  lemma mset_union_1_elem1[simp]: "({#a#} = M+{#b#}) = (a=b & M={#})" proof
    assume A: "{#a#} = M+{#b#}"
    from A have "size {#a#} = size (M+{#b#})" by simp
    hence "1 = 1 + size M" by auto
    hence "M={#}" by auto
    moreover with A have "a=b" by auto
    ultimately show "a=b & M={#}" by auto
  next
    assume "a = b \<and> M = {#}"
    thus "{#a#} = M+{#b#}" by auto
  qed

  lemma mset_union_1_elem2[simp]: "({#a#} = {#b#}+M) = (a=b & M={#})" using mset_union_1_elem1
    by (simp add: union_ac)

  lemma mset_union_1_elem3[simp]: "(M+{#b#}={#a#}) = (b=a & M={#})"
    by (auto dest: sym)
  lemma mset_union_1_elem4[simp]: "({#b#}+M={#a#}) = (b=a & M={#})" using mset_union_1_elem3
    by (simp add: union_ac)

  lemma mset_inter_1elem1[simp]: assumes A: "~(a :# B)" shows "{#a#} #\<inter> B = {#}" proof (unfold multiset_inter_def)
    from A have "{#a#} - B = {#a#}" by simp
    thus "{#a#} - ({#a#} - B) = {#}" by simp
  qed

  lemma mset_inter_1elem2[simp]: "~(a :# B) \<Longrightarrow> B #\<inter> {#a#} = {#}" proof -
    assume "~(a :# B)"
    hence "{#a#} #\<inter> B = {#}" by simp
    thus ?thesis by (simp add: multiset_inter_commute)
  qed

  lemmas mset_neutral_cancel1 = union_left_cancel[where N="{#}", simplified] union_right_cancel[where N="{#}", simplified]
  declare mset_neutral_cancel1[simp]

  lemma mset_neutral_cancel2[simp]: "(c=n+c) = (n={#})" "(c=c+n) = (n={#})"
    apply (auto simp add: union_ac)
    apply (subgoal_tac "c+n=c", simp_all)+
    done



  (* TODO: The proof seems too complicated, there should be an easier one ! *)
  lemma mset_union_2_elem: "{#a#}+{#b#} = M + {#c#} \<Longrightarrow> {#a#}=M & b=c | a=c & {#b#}=M" 
  proof -
    assume A: "{#a#}+{#b#} = M + {#c#}"
    hence "{#a#}+{#b#}-{#b#} = M + {#c#} - {#b#}" by auto
    hence AEQ: "{#a#} = M + {#c#} - {#b#}" by (auto simp add: union_assoc)
    { assume "c=b"
      with AEQ have "{#a#} = M" by auto  
    } moreover {
      from A have "{#b#}+{#a#} = M + {#c#}" by (auto simp add: union_commute)
      moreover assume "a=c"
      ultimately have "{#b#} = M" by auto
    } moreover {
      assume NEQ: "c~=b & a~=c"
      from A have "{#a#}+{#b#}-{#c#} = M + {#c#}-{#c#}" by auto
      hence "{#a#}+{#b#}-{#c#} = M" by (auto simp add: union_assoc)
      with NEQ have "{#a#}-{#c#}+{#b#} = M" by (subgoal_tac "~ (c :# {#b#})", auto simp add: multiset_union_diff_commute)
      with NEQ have "{#a#}+{#b#} = M" by (subgoal_tac "~(a :# {#c#})", auto)
      hence S1: "size M = 2" by auto
      moreover from A have "size ({#a#}+{#b#}) = size (M + {#c#})" by auto
      hence "size M = 1" by auto
      ultimately have "False" by simp
    }
    ultimately show ?thesis by blast
  qed

declare insert_DiffM[simp]

  lemma mset_un_iff: "(a :# A + B) = (a :# A | a :# B)"
    by (simp)
  lemma mset_un_cases[cases set, case_names left right]: "\<lbrakk>a :# A + B; a:#A \<Longrightarrow> P; a:#B \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
    by (auto)

  lemma mset_unplusm_dist_cases[cases set, case_names left right]:
    assumes A: "{#s#}+A = B+C"
    assumes L: "\<lbrakk>B={#s#}+(B-{#s#}); A=(B-{#s#})+C\<rbrakk> \<Longrightarrow> P"
    assumes R: "\<lbrakk>C={#s#}+(C-{#s#}); A=B+(C-{#s#})\<rbrakk> \<Longrightarrow> P" 
    shows P
  proof -
    from A[symmetric] have "s :# B+C" by simp
    thus ?thesis proof (cases rule: mset_un_cases)
      case left hence 1: "B={#s#}+(B-{#s#})" by simp
      with A have "{#s#}+A = {#s#}+((B-{#s#})+C)" by (simp add: union_ac)
      hence 2: "A = (B-{#s#})+C" by (simp)
      from L[OF 1 2] show ?thesis .
    next
      case right hence 1: "C={#s#}+(C-{#s#})" by simp
      with A have "{#s#}+A = {#s#}+(B+(C-{#s#}))" by (simp add: union_ac)
      hence 2: "A = B+(C-{#s#})" by (simp)
      from R[OF 1 2] show ?thesis .
    qed
  qed

  lemma mset_unplusm_dist_cases2[cases set, case_names left right]:
    assumes A: "B+C = {#s#}+A"
    assumes L: "\<lbrakk>B={#s#}+(B-{#s#}); A=(B-{#s#})+C\<rbrakk> \<Longrightarrow> P"
    assumes R: "\<lbrakk>C={#s#}+(C-{#s#}); A=B+(C-{#s#})\<rbrakk> \<Longrightarrow> P" 
    shows P
    using mset_unplusm_dist_cases[OF A[symmetric]] L R by blast

  lemma mset_single_cases[cases set, case_names loc env]: 
    assumes A: "{#s#}+c = {#r'#}+c'" 
    assumes CASES: "\<lbrakk>s=r'; c=c'\<rbrakk> \<Longrightarrow> P" "\<lbrakk>c'={#s#}+(c'-{#s#}); c={#r'#}+(c-{#r'#}); c-{#r'#} = c'-{#s#} \<rbrakk> \<Longrightarrow> P" 
    shows "P"
  proof -
    { assume CASE: "s=r'"
      with A have "c=c'" by simp
      with CASE CASES have ?thesis by auto
    } moreover {
      assume CASE: "s\<noteq>r'"
      have "s:#{#s#}+c" by simp
      with A have "s:#{#r'#}+c'" by simp
      with CASE have "s:#c'" by (auto elim!: mset_un_cases split: split_if_asm)
      from insert_DiffM[OF this, symmetric] have 1: "c' = {#s#} + (c' - {#s#})" .
      with A have "{#s#}+c = {#s#}+({#r'#}+(c' - {#s#}))" by (auto simp add: union_ac)
      hence 2: "c={#r'#}+(c' - {#s#})" by (auto)
      hence 3: "c-{#r'#} = (c' - {#s#})" by auto
      from 1 2 3 CASES have ?thesis by auto
    } ultimately show ?thesis by blast
  qed

  lemma mset_single_cases'[cases set, case_names loc env]: 
    assumes A: "{#s#}+c = {#r'#}+c'" 
    assumes CASES: "\<lbrakk>s=r'; c=c'\<rbrakk> \<Longrightarrow> P" "!!cc. \<lbrakk>c'={#s#}+cc; c={#r'#}+cc; c'-{#s#}=cc; c-{#r'#}=cc\<rbrakk> \<Longrightarrow> P" 
    shows "P"
    using A  CASES by (auto elim!: mset_single_cases)

  lemma mset_single_cases2[cases set, case_names loc env]: 
    assumes A: "c+{#s#} = c'+{#r'#}" 
    assumes CASES: "\<lbrakk>s=r'; c=c'\<rbrakk> \<Longrightarrow> P" "\<lbrakk>c'=(c'-{#s#})+{#s#}; c=(c-{#r'#})+{#r'#}; c-{#r'#} = c'-{#s#} \<rbrakk> \<Longrightarrow> P" 
    shows "P" 
  proof -
    from A have "{#s#}+c = {#r'#}+c'" by (simp add: union_ac)
    thus ?thesis proof (cases rule: mset_single_cases)
      case loc with CASES show ?thesis by simp
    next
      case env with CASES show ?thesis by (simp add: union_ac)
    qed
  qed

  lemma mset_single_cases2'[cases set, case_names loc env]: 
    assumes A: "c+{#s#} = c'+{#r'#}" 
    assumes CASES: "\<lbrakk>s=r'; c=c'\<rbrakk> \<Longrightarrow> P" "!!cc. \<lbrakk>c'=cc+{#s#}; c=cc+{#r'#}; c'-{#s#}=cc; c-{#r'#}=cc\<rbrakk> \<Longrightarrow> P" 
    shows "P"
    using A  CASES by (auto elim!: mset_single_cases2)

  lemma mset_un_single_un_cases[consumes 1, case_names left right]: assumes A: "A+{#a#} = B+C" and CASES: "\<lbrakk>a:#B; A=(B-{#a#})+C\<rbrakk> \<Longrightarrow> P" "\<lbrakk>a:#C; A=B+(C-{#a#})\<rbrakk> \<Longrightarrow> P" shows "P"
  proof -
    have "a:#A+{#a#}" by simp
    with A have "a:#B+C" by auto
    thus ?thesis proof (cases rule: mset_un_cases)
      case left hence "B=B-{#a#}+{#a#}" by auto
      with A have "A+{#a#} = (B-{#a#})+C+{#a#}" by (auto simp add: union_ac)
      hence "A=(B-{#a#})+C" by simp
      with CASES(1)[OF left] show ?thesis by blast
    next
      case right hence "C=C-{#a#}+{#a#}" by auto
      with A have "A+{#a#} = B+(C-{#a#})+{#a#}" by (auto simp add: union_ac)
      hence "A=B+(C-{#a#})" by simp
      with CASES(2)[OF right] show ?thesis by blast
    qed
  qed

      (* TODO: Can this proof be done more automatically ? *)
  lemma mset_distrib[consumes 1, case_names dist]: assumes A: "(A::'a multiset)+B = M+N" "!!Am An Bm Bn. \<lbrakk>A=Am+An; B=Bm+Bn; M=Am+Bm; N=An+Bn\<rbrakk> \<Longrightarrow> P" shows "P"
  proof -
    { 
      fix X
      have "!!A B M N P. \<lbrakk> (X::'a multiset)=A+B; A+B = M+N; !!Am An Bm Bn. \<lbrakk>A=Am+An; B=Bm+Bn; M=Am+Bm; N=An+Bn\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
      proof (induct X)
        case empty thus ?case by simp
      next
        case (add X x A B M N) 
        from add(2,3) have MN: "X+{#x#} = M+N" by simp
        from add(2) show ?case proof (cases rule: mset_un_single_un_cases)
          case left from MN show ?thesis proof (cases rule: mset_un_single_un_cases[case_names left' right'])
            case left' with left have "X=A-{#x#}+B" "A-{#x#}+B = M-{#x#}+N" by simp_all
            from "add.hyps"[OF this] obtain Am An Bm Bn where "A - {#x#} = Am + An" "B = Bm + Bn" "M - {#x#} = Am + Bm" "N = An + Bn" .
            hence "A - {#x#} + {#x#} = Am+{#x#} + An" "B = Bm + Bn" "M - {#x#}+{#x#} = Am+{#x#} + Bm" "N = An + Bn" by (simp_all add: union_ac)
            with left(1) left'(1) show ?thesis using "add.prems"(3) by auto
          next
            case right' with left have "X=A-{#x#}+B" "A-{#x#}+B = M+(N-{#x#})" by simp_all
            from "add.hyps"[OF this] obtain Am An Bm Bn where "A - {#x#} = Am + An" "B = Bm + Bn" "M = Am + Bm" "N-{#x#} = An + Bn" .
            hence "A - {#x#} + {#x#} = Am + (An+{#x#})" "B = Bm + Bn" "M = Am + Bm" "N - {#x#}+{#x#} = (An+{#x#}) + Bn" by (simp_all add: union_ac)
            with left(1) right'(1) show ?thesis using "add.prems"(3) by auto
          qed
        next
          case right from MN show ?thesis proof (cases rule: mset_un_single_un_cases[case_names left' right'])
            case left' with right have "X=A+(B-{#x#})" "A+(B-{#x#}) = M-{#x#}+N" by simp_all
            from "add.hyps"[OF this] obtain Am An Bm Bn where "A = Am + An" "B-{#x#} = Bm + Bn" "M - {#x#} = Am + Bm" "N = An + Bn" .
            hence "A = Am + An" "B-{#x#}+{#x#} = Bm+{#x#} + Bn" "M - {#x#}+{#x#} = Am + (Bm+{#x#})" "N = An + Bn" by (simp_all add: union_ac)
            with right(1) left'(1) show ?thesis using "add.prems"(3) by auto
          next
            case right' with right have "X=A+(B-{#x#})" "A+(B-{#x#}) = M+(N-{#x#})" by simp_all
            from "add.hyps"[OF this] obtain Am An Bm Bn where "A = Am + An" "B-{#x#} = Bm + Bn" "M = Am + Bm" "N-{#x#} = An + Bn" .
            hence "A = Am + An" "B-{#x#}+{#x#} = Bm + (Bn+{#x#})" "M = Am + Bm" "N - {#x#}+{#x#} = An + (Bn+{#x#})" by (simp_all add: union_ac)
            with right(1) right'(1) show ?thesis using "add.prems"(3) by auto
          qed
        qed
      qed
    } with A show ?thesis by blast
  qed


subsubsection {* Singleton multisets *}   
  lemma mset_singletonI[intro!]: "a :# {#a#}"
    by auto

  lemma mset_singletonD[dest!]: "b :# {#a#} \<Longrightarrow> b=a" 
    apply(cases "a=b")
    apply(auto)
  done

lemma mset_size_le1_cases[case_names empty singleton,consumes 1]: "\<lbrakk> size M \<le> Suc 0; M={#} \<Longrightarrow> P; !!m. M={#m#} \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (cases M) auto

lemma diff_union_single_conv2: "a :# J \<Longrightarrow> J + I - {#a#} = (J - {#a#}) + I" using diff_union_single_conv[of J a I]
  by (simp add: union_ac)

lemmas diff_union_single_convs = diff_union_single_conv diff_union_single_conv2

lemma mset_contains_eq: "(m:#M) = ({#m#}+(M-{#m#})=M)" proof (auto)
  assume "{#m#} + (M - {#m#}) = M"
  moreover have "m :# {#m#} + (M - {#m#})" by simp
  ultimately show "m:#M" by simp
qed


subsubsection {* Pointwise ordering *}


  lemma mset_empty_minimal[simp, intro!]: "{#} \<le># c"
    by (unfold subseteq_mset_def, auto)
  lemma mset_empty_least[simp]: "c \<le># {#} = (c={#})"
    by (unfold subseteq_mset_def, auto)
  lemma mset_empty_leastI[intro!]: "c={#} \<Longrightarrow> c \<le># {#}"
    by (simp only: mset_empty_least)

  lemma mset_le_incr_right1: "(a::'a multiset)\<le>#b \<Longrightarrow> a\<le>#b+c" using mset_le_mono_add[of a b "{#}" c, simplified] .
  lemma mset_le_incr_right2: "(a::'a multiset)\<le>#b \<Longrightarrow> a\<le>#c+b" using mset_le_incr_right1
    by (auto simp add: union_commute)
  lemmas mset_le_incr_right = mset_le_incr_right1 mset_le_incr_right2

  lemma mset_le_decr_left1: "(a::'a multiset)+c\<le>#b \<Longrightarrow> a\<le>#b" using mset_le_incr_right1 mset_le_mono_add_right_cancel
    by blast
  lemma mset_le_decr_left2: "c+(a::'a multiset)\<le>#b \<Longrightarrow> a\<le>#b" using mset_le_decr_left1
    by (auto simp add: union_ac)
  lemmas mset_le_decr_left = mset_le_decr_left1 mset_le_decr_left2
  
  lemma mset_le_single_conv[simp]: "({#e#}\<le>#M) = (e:#M)"
    by (unfold subseteq_mset_def) auto

  lemma mset_le_trans_elem: "\<lbrakk>e :# c; c \<le># c'\<rbrakk> \<Longrightarrow> e :# c'" using subset_mset.order_trans[of "{#e#}" c c', simplified]
    by assumption

  lemma mset_le_subtract: "(A::'a multiset)\<le>#B \<Longrightarrow> A-C \<le># B-C"
    apply (unfold subseteq_mset_def)
    apply auto
    apply (subgoal_tac "count A a \<le> count B a")
    apply arith
    apply simp
    done

  lemma mset_le_union: "(A::'a multiset)+B \<le># C \<Longrightarrow> A\<le>#C \<and> B\<le>#C"
    by (auto dest: mset_le_decr_left)

  lemma mset_le_subtract_left: "(A::'a multiset)+B \<le># X \<Longrightarrow> B \<le># X-A \<and> A\<le>#X"
    by (auto dest: mset_le_subtract[of "A+B" "X" "A"] mset_le_union)
  lemma mset_le_subtract_right: "(A::'a multiset)+B \<le># X \<Longrightarrow> A \<le># X-B \<and> B\<le>#X"
    by (auto dest: mset_le_subtract[of "A+B" "X" "B"] mset_le_union)
  
  lemma mset_le_addE: "\<lbrakk> (xs::'a multiset) \<le># ys; !!zs. ys=xs+zs \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P" using mset_le_exists_conv
    by blast

  lemma mset_le_sub_add_eq[simp,intro]: "(A::'a multiset)\<le>#B \<Longrightarrow> B-A+A = B"
    by (auto elim: mset_le_addE simp add: union_ac)

  lemma mset_2dist2_cases:
    assumes A: "{#a#}+{#b#} \<le># A+B"
    assumes CASES: "{#a#}+{#b#} \<le># A \<Longrightarrow> P" "{#a#}+{#b#} \<le># B \<Longrightarrow> P" "\<lbrakk>a :# A; b :# B\<rbrakk> \<Longrightarrow> P" "\<lbrakk>a :# B; b :# A\<rbrakk> \<Longrightarrow> P"
    shows "P"
  proof -
    { assume C: "a :# A" "b :# A-{#a#}" 
      with mset_le_mono_add[of "{#a#}" "{#a#}" "{#b#}" "A-{#a#}"] have "{#a#}+{#b#} \<le># A" by auto
    } moreover {
      assume C: "a :# A" "\<not> (b :# A-{#a#})"
      with A have "b:#B" by (unfold subseteq_mset_def) (auto split: split_if_asm)
    } moreover {
      assume C: "\<not> (a :# A)" "b :# B-{#a#}"
      with A have "a :# B" by (unfold subseteq_mset_def) (auto split: split_if_asm)
      with C mset_le_mono_add[of "{#a#}" "{#a#}" "{#b#}" "B-{#a#}"] have "{#a#}+{#b#} \<le># B" by auto
    } moreover {
      assume C: "\<not> (a :# A)" "\<not> (b :# B-{#a#})"
      with A have "a:#B \<and> b:#A" by (unfold subseteq_mset_def) (auto split: split_if_asm)
    } ultimately show P using CASES by blast
  qed

  lemma mset_union_subset: "(A::'a multiset)+B \<le># C \<Longrightarrow> A\<le>#C \<and> B\<le># C"
    apply (unfold subseteq_mset_def)
    apply auto
    apply (subgoal_tac "count A a + count B a \<le> count C a", arith, simp)+
    done

  lemma mset_union_subset_s: "{#a#}+B \<le># C \<Longrightarrow> a :# C \<and> B \<le># C"
    by (auto dest: mset_union_subset)

  lemma mset_le_eq_refl: "(a::'a multiset)=b \<Longrightarrow> a\<le>#b"
    by simp

  lemma mset_singleton_eq[simplified,simp]: "a :# {#b#} = (a=b)"
    by auto -- {* The simplification is here due to the lemma @{thm [source] "Multiset.count_single"}, that will be applied first deleting any application potential for this rule*}
  lemma mset_le_single_single[simp]: "({#a#} \<le># {#b#}) = (a=b)"
    by auto

  lemma mset_le_single_conv1[simp]: "(M+{#a#} \<le># {#b#}) = (M={#} \<and> a=b)"
  proof (auto) 
    assume A: "M+{#a#} \<le># {#b#}" thus "a=b" by (auto dest: mset_le_decr_left2)
    with A mset_le_mono_add_right_cancel[of M "{#a#}" "{#}", simplified] show "M={#}" by blast
  qed
  
  lemma mset_le_single_conv2[simp]: "({#a#}+M \<le># {#b#}) = (M={#} \<and> a=b)"
    by (simp add: union_ac)
  
  lemma mset_le_single_cases[consumes 1, case_names empty singleton]: "\<lbrakk>M\<le>#{#a#}; M={#} \<Longrightarrow> P; M={#a#} \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
    by (induct M) auto
      
  lemma mset_le_distrib[consumes 1, case_names dist]: "\<lbrakk>X\<le>#(A::'a multiset)+B; !!Xa Xb. \<lbrakk>X=Xa+Xb; Xa\<le>#A; Xb\<le>#B\<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
    by (auto elim!: mset_le_addE mset_distrib)

  lemma mset_le_mono_add_single: "\<lbrakk>a :# ys; b :# ws\<rbrakk> \<Longrightarrow> {#a#} + {#b#} \<le># ys + ws" using mset_le_mono_add[of "{#a#}" _ "{#b#}", simplified] .

  lemma mset_size1elem: "\<lbrakk>size P \<le> 1; q :# P\<rbrakk> \<Longrightarrow> P={#q#}"
    by (auto elim: mset_size_le1_cases)
  lemma mset_size2elem: "\<lbrakk>size P \<le> 2; {#q#}+{#q'#} \<le># P\<rbrakk> \<Longrightarrow> P={#q#}+{#q'#}"
    by (auto elim: mset_le_addE)


subsubsection {* Image under function *}

inductive_set 
  mset_map_Set :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a multiset \<times> 'b multiset) set"
  for f:: "'a \<Rightarrow> 'b"
  where
  mset_map_Set_empty: "({#},{#})\<in>mset_map_Set f"
  | mset_map_Set_add: "(A,B)\<in>mset_map_Set f \<Longrightarrow> (A+{#a#},B+{#f a#})\<in>mset_map_Set f"

lemma mset_map_Set_empty_simps[simp]: "(({#},B)\<in>mset_map_Set f) = (B={#})" "((A,{#})\<in>mset_map_Set f) = (A={#})"
  by (auto elim: mset_map_Set.cases intro: mset_map_Set_empty)

lemma mset_map_Set_single_left[simp]: "(({#a#},B)\<in>mset_map_Set f) = (B={#f a#})"
  by (auto elim: mset_map_Set.cases intro: mset_map_Set_add[of "{#}" "{#}", simplified])
lemma mset_map_Set_single_rightE[cases set, case_names orig]: "\<lbrakk>(A,{#b#})\<in>mset_map_Set f; !!a. \<lbrakk>A={#a#}; b=f a\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto elim: mset_map_Set.cases)

lemma mset_map_Set_sizes: "(A,B)\<in>mset_map_Set f \<Longrightarrow> size A = size B"
  by (induct rule: mset_map_Set.induct) auto

text {* Intuitively, this lemma allows one to choose a single image element corresponding to an original element *}
lemma mset_map_Set_choose[cases set, case_names choice]: assumes A: "(A+{#a#},B)\<in>mset_map_Set f" "!!B'. \<lbrakk>B=B'+{#f a#}; (A,B')\<in>mset_map_Set f\<rbrakk> \<Longrightarrow> P" shows "P" 
proof -
  { fix n
    have "\<lbrakk>size B=n; (A+{#a#},B)\<in>mset_map_Set f; !!B'. \<lbrakk>B=B'+{#f a#}; (A,B')\<in>mset_map_Set f\<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P" proof (induct n arbitrary: A a B P)

    (*have "!!A a B P. \<lbrakk>size B=n; (A+{#a#},B)\<in>mset_map_Set f; !!B'. \<lbrakk>B=B'+{#f a#}; (A,B')\<in>mset_map_Set f\<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P" proof (induct n)*)
      case 0 thus ?case by simp
    next
      case (Suc n') from Suc.prems(2) show ?case proof (cases rule: mset_map_Set.cases)
        case mset_map_Set_empty hence False by simp thus ?thesis ..
      next
        case (mset_map_Set_add A' B' a') 
        hence "A+{#a#}=A'+{#a'#}" by simp
        thus ?thesis proof (cases rule: mset_single_cases2')
          case loc with mset_map_Set_add Suc.prems(3) show ?thesis by auto
        next
          case (env A'') 
          from Suc.prems(1) mset_map_Set_add(2) have SIZE: "size B' = n'" by auto
          from mset_map_Set_add env have MM: "(A'' + {#a#}, B') \<in> mset_map_Set f" by simp
          from Suc.hyps[OF SIZE MM] obtain B'' where B'': "B'=B''+{#f a#}" "(A'',B'')\<in>mset_map_Set f" by blast
          from mset_map_Set.mset_map_Set_add[OF B''(2)] env(2) have "(A, B'' + {#f a'#}) \<in> mset_map_Set f" by simp
          moreover from B''(1) mset_map_Set_add have "B=B'' + {#f a'#} + {#f a#}" by (simp add: union_ac)
          ultimately show ?thesis using Suc.prems(3) by blast
        qed
      qed
    qed
  } with A show P by blast
qed

lemma mset_map_Set_unique: "!!B B'. \<lbrakk>(A,B)\<in>mset_map_Set f; (A,B')\<in>mset_map_Set f\<rbrakk> \<Longrightarrow> B=B'"
  by (induct A) (auto elim!: mset_map_Set_choose)
lemma mset_map_Set_surjective: "\<lbrakk> !!B. (A,B)\<in>mset_map_Set f \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (induct A) (auto intro: mset_map_Set_add)


definition
  mset_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a multiset \<Rightarrow> 'b multiset" (infixr "`#" 90)
  where
  "f `# A == (THE B. (A,B)\<in>mset_map_Set f)"


interpretation mset_map: su_rel_fun "mset_map_Set f" "op `# f"
  apply (rule su_rel_fun.intro)
  apply (erule mset_map_Set_unique, assumption)
  apply (erule mset_map_Set_surjective)
  apply (rule mset_map_def)
  done
  
text {* Transfer the defining equations *}
lemma mset_map_empty[simp]: "f `# {#} = {#}"
  apply (subst mset_map.repr)
  apply (rule mset_map_Set_empty)
  done

lemma mset_map_add[simp]: "f `# (A+{#a#}) = f `# A + {#f a#}" "f `# ({#a#}+A) = {#f a#} + f `# A"
  by (auto simp add: mset_map.repr union_commute intro: mset_map_Set_add mset_map.repr1)

text {* Transfer some other lemmas *}
lemma mset_map_single_rightE[consumes 1, case_names orig]: "\<lbrakk>f `# P = {#y#}; !!x. \<lbrakk> P={#x#}; f x = y \<rbrakk> \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  by (auto simp add: mset_map.repr elim: mset_map_Set_single_rightE)

text {* And show some further equations *}
lemma mset_map_single[simp]: "f `# {#a#} = {#f a#}" using mset_map_add(1)[where A="{#}", simplified] .

lemma mset_map_union: "!!B. f `# (A+B) = f `# A + f `# B"
  by (induct A) (auto simp add: union_ac)

lemma mset_map_size: "size A = size (f `# A)"
  by (induct A) auto

lemma mset_map_empty_eq[simp]: "(f `# P = {#}) = (P={#})" using mset_map_size[of P f]
  by auto

lemma mset_map_le: "!!B. A \<le># B \<Longrightarrow> f `# A \<le># f `# B" proof (induct A)
  case empty thus ?case by simp
next
  case (add A x B)
  hence "A\<le>#B-{#x#}" and SM: "{#x#}\<le>#B" using mset_le_subtract_right by (fastforce+)
  with "add.hyps" have "f `# A \<le># f `# (B-{#x#})" by blast
  hence "f `# (A+{#x#}) \<le># f `# (B-{#x#}) + {#f x#}" by auto
  also have "\<dots> = f `# (B-{#x#}+{#x#})" by simp
  also with SM have "\<dots> = f `# B" by simp
  finally show ?case .
qed

lemma mset_map_split_orig: "!!M1 M2. \<lbrakk>f `# P = M1+M2; !!P1 P2. \<lbrakk>P=P1+P2; f `# P1 = M1; f `# P2 = M2\<rbrakk> \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  apply (induct P)
  apply fastforce
  apply (fastforce elim!: mset_un_single_un_cases simp add: union_ac) (* TODO: This proof need's quite long. Try to write a faster one. *)
  done

lemma mset_map_id: "\<lbrakk>!!x. f (g x) = x\<rbrakk> \<Longrightarrow> f `# g `# X = X"
  by (induct X) auto

text {* The following is a very specialized lemma. Intuitively, it splits the original multiset *}
text {* The following is a very specialized   by a splitting of some pointwise supermultiset of its image.

  Application:
  This lemma came in handy when proving the correctness of a constraint system that collects at most k sized submultisets of the sets of spawned threads.
*}
lemma mset_map_split_orig_le: assumes A: "f `# P \<le># M1+M2" and EX: "!!P1 P2. \<lbrakk>P=P1+P2; f `# P1 \<le># M1; f `# P2 \<le># M2\<rbrakk> \<Longrightarrow> Q" shows "Q"
  using A EX by (auto elim: mset_le_distrib mset_map_split_orig)


subsection {* Lists *}

subsubsection {* Reverse lists *}
  lemma list_rev_decomp[rule_format]: "l~=[] \<longrightarrow> (EX ll e . l = ll@[e])"
    apply(induct_tac l)
    apply(auto)
  done
    
  (* Was already there as rev_induct
  lemma list_rev_induct: "\<lbrakk>P []; !! l e . P l \<Longrightarrow> P (l@[e]) \<rbrakk> \<Longrightarrow> P l"
    by (blast intro: rev_induct)
  proof (induct l rule: measure_induct[of length])
    fix x :: "'a list"
    assume A: "\<forall>y. length y < length x \<longrightarrow> P [] \<longrightarrow> (\<forall>x xa. P (x::'a list) \<longrightarrow> P (x @ [xa])) \<longrightarrow> P y" "P []" and IS: "\<And>l e. P l \<Longrightarrow> P (l @ [e])"
    show "P x" proof (cases "x=[]")
      assume "x=[]" with A show ?thesis by simp
    next
      assume CASE: "x~=[]"
      then obtain xx e where DECOMP: "x=xx@[e]" by (blast dest: list_rev_decomp)
      hence LEN: "length xx < length x" by auto
      with A IS have "P xx" by auto
      with IS have "P (xx@[e])" by auto
      with DECOMP show ?thesis by auto
    qed
  qed
  *)

  text {* Caution: Same order of case variables in snoc-case as @{thm [source] rev_exhaust}, the other way round than @{thm [source] rev_induct} ! *}
  lemma length_compl_rev_induct[case_names Nil snoc]: "\<lbrakk>P []; !! l e . \<lbrakk>!! ll . length ll <= length l \<Longrightarrow> P ll\<rbrakk> \<Longrightarrow> P (l@[e])\<rbrakk> \<Longrightarrow> P l"
    apply(induct_tac l rule: length_induct)
    apply(case_tac "xs" rule: rev_cases)
    apply(auto)
  done

  lemma list_append_eq_Cons_cases: "\<lbrakk>ys@zs = x#xs; \<lbrakk>ys=[]; zs=x#xs\<rbrakk> \<Longrightarrow> P; !!ys'. \<lbrakk> ys=x#ys'; ys'@zs=xs \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
    by (auto iff add: append_eq_Cons_conv)
  lemma list_Cons_eq_append_cases: "\<lbrakk>x#xs = ys@zs; \<lbrakk>ys=[]; zs=x#xs\<rbrakk> \<Longrightarrow> P; !!ys'. \<lbrakk> ys=x#ys'; ys'@zs=xs \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
    by (auto iff add: Cons_eq_append_conv)

subsubsection "folding"

text "Ugly lemma about foldl over associative operator with left and right neutral element"
lemma foldl_A1_eq: "!!i. \<lbrakk> !! e. f n e = e; !! e. f e n = e; !!a b c. f a (f b c) = f (f a b) c \<rbrakk> \<Longrightarrow> foldl f i ww = f i (foldl f n ww)"
proof (induct ww)
  case Nil thus ?case by simp
next
  case (Cons a ww i) note IHP[simplified]=this
  have "foldl f i (a # ww) = foldl f (f i a) ww" by simp
  also from IHP have "\<dots> = f (f i a) (foldl f n ww)" by blast
  also from IHP(4) have "\<dots> = f i (f a (foldl f n ww))" by simp
  also from IHP(1)[OF IHP(2,3,4), where i=a] have "\<dots> = f i (foldl f a ww)" by simp
  also from IHP(2)[of a] have "\<dots> = f i (foldl f (f n a) ww)" by simp
  also have "\<dots> = f i (foldl f n (a#ww))" by simp
  finally show ?case .
qed

lemmas foldl_conc_empty_eq = foldl_A1_eq[of "op @" "[]", simplified]
lemmas foldl_un_empty_eq = foldl_A1_eq[of "op \<union>" "{}", simplified, OF Un_assoc[symmetric]]

lemma foldl_set: "foldl (op \<union>) {} l = \<Union>{x. x\<in>set l}"
  apply (induct l)
  apply simp_all
  apply (subst foldl_un_empty_eq)
  apply auto
  done


subsubsection {* Miscellaneous *}
  lemma length_compl_induct[case_names Nil Cons]: "\<lbrakk>P []; !! e l . \<lbrakk>!! ll . length ll <= length l \<Longrightarrow> P ll\<rbrakk> \<Longrightarrow> P (e#l)\<rbrakk> \<Longrightarrow> P l"
    apply(induct_tac l rule: length_induct)
    apply(case_tac "xs")
    apply(auto)
  done


  text {* Simultaneous induction over two lists, prepending an element to one of the lists in each step *}
  lemma list_2pre_induct[case_names base left right]: assumes BASE: "P [] []" and LEFT: "!!e w1' w2. P w1' w2 \<Longrightarrow> P (e#w1') w2" and RIGHT: "!!e w1 w2'. P w1 w2' \<Longrightarrow> P w1 (e#w2')" shows "P w1 w2" 
  proof -
    { -- "The proof is done by induction over the sum of the lengths of the lists"
      fix n
      have "!!w1 w2. \<lbrakk>length w1 + length w2 = n; P [] []; !!e w1' w2. P w1' w2 \<Longrightarrow> P (e#w1') w2; !!e w1 w2'. P w1 w2' \<Longrightarrow> P w1 (e#w2') \<rbrakk> \<Longrightarrow> P w1 w2 " 
        apply (induct n)
        apply simp
        apply (case_tac w1)
        apply auto
        apply (case_tac w2)
        apply auto
        done
    } from this[OF _ BASE LEFT RIGHT] show ?thesis by blast
  qed


  lemma list_decomp_1: "length l=1 \<Longrightarrow> EX a . l=[a]"
    by (case_tac l, auto)

  lemma list_decomp_2: "length l=2 \<Longrightarrow> EX a b . l=[a,b]"
    by (case_tac l, auto simp add: list_decomp_1)


  lemma drop_all_conc: "drop (length a) (a@b) = b"
    by (simp)

  lemma list_rest_coinc: "\<lbrakk>length s2 <= length s1; s1@r1 = s2@r2\<rbrakk> \<Longrightarrow> EX r1p . r2=r1p@r1"
  proof -
    assume A: "length s2 <= length s1" "s1@r1 = s2@r2"
    hence "r1 = drop (length s1) (s2@r2)" by (auto simp only:drop_all_conc dest: sym)
    moreover from A have "length s1 = length s1 - length s2 + length s2" by arith
    ultimately have "r1 = drop ((length s1 - length s2)) r2" by (auto)
    hence "r2 = take ((length s1 - length s2)) r2 @ r1" by auto
    thus ?thesis by auto
  qed

  lemma list_tail_coinc: "n1#r1 = n2#r2 \<Longrightarrow> n1=n2 & r1=r2"
    by (auto)


  lemma last_in_set[intro]: "\<lbrakk>l\<noteq>[]\<rbrakk> \<Longrightarrow> last l \<in> set l"
    by (induct l) auto

subsection {* Induction on nat *}
  lemma nat_compl_induct[case_names 0 Suc]: "\<lbrakk>P 0; !! n . ALL nn . nn <= n \<longrightarrow> P nn \<Longrightarrow> P (Suc n)\<rbrakk> \<Longrightarrow> P n"
    apply(induct_tac n rule: nat_less_induct)
    apply(case_tac n)
    apply(auto)
  done


subsection {* Functions of type @{typ "bool\<Rightarrow>bool"}*}
  lemma boolfun_cases_helper: "g=(\<lambda>x. False) | g=(\<lambda>x. x) | g=(\<lambda>x. True) | g= (\<lambda>x. \<not>x)" 
  proof -
    { assume "g False" "g True"
      hence "g = (\<lambda>x. True)" by (rule_tac ext, case_tac x, auto)
    } moreover {
      assume "g False" "\<not>g True"
      hence "g = (\<lambda>x. \<not>x)" by (rule_tac ext, case_tac x, auto)
    } moreover {
      assume "\<not>g False" "g True"
      hence "g = (\<lambda>x. x)" by (rule_tac ext, case_tac x, auto)
    } moreover {
      assume "\<not>g False" "\<not>g True"
      hence "g = (\<lambda>x. False)" by (rule_tac ext, case_tac x, auto)
    } ultimately show ?thesis by fast
  qed

  lemma boolfun_cases[case_names False Id True Neg]: "\<lbrakk>g=(\<lambda>x. False) \<Longrightarrow> P g; g=(\<lambda>x. x) \<Longrightarrow> P g; g=(\<lambda>x. True) \<Longrightarrow> P g; g=(\<lambda>x. \<not>x) \<Longrightarrow> P g\<rbrakk> \<Longrightarrow> P g"
  proof -
    note boolfun_cases_helper[of g]
    moreover assume "g=(\<lambda>x. False) \<Longrightarrow> P g" "g=(\<lambda>x. x) \<Longrightarrow> P g" "g=(\<lambda>x. True) \<Longrightarrow> P g" "g=(\<lambda>x. \<not>x) \<Longrightarrow> P g"
    ultimately show ?thesis by fast
  qed


  subsection {* Definite and indefinite description *}
  text "Combined definite and indefinite description for binary predicate"
  lemma some_theI: assumes EX: "\<exists>a b . P a b" and BUN: "!! b1 b2 . \<lbrakk>\<exists>a . P a b1; \<exists>a . P a b2\<rbrakk> \<Longrightarrow> b1=b2" 
    shows "P (SOME a . \<exists>b . P a b) (THE b . \<exists>a . P a b)"
  proof -
    from EX have "EX b . P (SOME a . EX b . P a b) b" by (rule someI_ex)
    moreover from EX have "EX b . EX a . P a b" by blast
    with BUN theI'[of "\<lambda>b . EX a . P a b"] have "EX a . P a (THE b . EX a . P a b)" by (unfold Ex1_def, blast)
    moreover note BUN
    ultimately show ?thesis by (fast)
  qed
  


end
