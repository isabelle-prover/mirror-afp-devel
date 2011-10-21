(*  Title:      JinjaThreads/Common/SemiType.thy
    Author:     Tobias Nipkow, Gerwin Klein, Andreas Lochbihler
*)

header {* 
  \isaheader{The Jinja Type System as a Semilattice} 
*}

theory SemiType imports
  "WellForm" 
  "../DFA/Semilattices"
begin

inductive_set
  widen1 :: "'a prog \<Rightarrow> (ty \<times> ty) set"
  and widen1_syntax :: "'a prog \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool" ("_ \<turnstile> _ <\<^sup>1 _" [71,71,71] 70)
  for P :: "'a prog"
where
  "P \<turnstile> C <\<^sup>1 D \<equiv> (C, D) \<in> widen1 P"

| widen1_Array_Object:
  "P \<turnstile> Array (Class Object) <\<^sup>1 Class Object"

| widen1_Array_Integer:
  "P \<turnstile> Array Integer <\<^sup>1 Class Object"

| widen1_Array_Boolean:
  "P \<turnstile> Array Boolean <\<^sup>1 Class Object"

| widen1_Array_Void:
  "P \<turnstile> Array Void <\<^sup>1 Class Object"

| widen1_Class: 
  "P \<turnstile> C \<prec>\<^sup>1 D \<Longrightarrow> P \<turnstile> Class C <\<^sup>1 Class D"

| widen1_Array_Array:
  "\<lbrakk> P \<turnstile> T <\<^sup>1 U; \<not> is_NT_Array T \<rbrakk> \<Longrightarrow> P \<turnstile> Array T <\<^sup>1 Array U"

abbreviation widen1_trancl :: "'a prog \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool" ("_ \<turnstile> _ <\<^sup>+ _" [71,71,71] 70) where
  "P \<turnstile> T <\<^sup>+ U \<equiv> (T, U) \<in> trancl (widen1 P)"

lemma widen1_Integer [iff]:
  "\<not> P \<turnstile> Integer <\<^sup>1 T"
  by(auto elim: widen1.cases)

lemma widen1_Boolean [iff]:
  "\<not> P \<turnstile> Boolean <\<^sup>1 T"
  by(auto elim: widen1.cases)

lemma widen1_Void [iff]:
  "\<not> P \<turnstile> Void <\<^sup>1 T"
  by(auto elim: widen1.cases)

lemma widen1_Class_Object [iff]:
  "\<not> P \<turnstile> Class Object <\<^sup>1 T"
  by(auto elim: widen1.cases)

lemma widen1_NT [simp]: "\<not> P \<turnstile> NT <\<^sup>1 U"
by(auto elim: widen1.cases)

lemma is_type_widen1: 
  assumes icO: "is_class P Object"
  shows "P \<turnstile> T <\<^sup>1 U \<Longrightarrow> is_type P T"
by(induct rule: widen1.induct)(auto intro: subcls_is_class icO split: ty.split dest: is_type_ground_type)

lemma widen1_NT_Array:
  assumes NT: "is_NT_Array T"
  shows "\<not> P \<turnstile> T\<lfloor>\<rceil> <\<^sup>1 U"
proof
  assume "P \<turnstile> T\<lfloor>\<rceil> <\<^sup>1 U"
  thus False using NT
    by(induct "T\<lfloor>\<rceil>" U arbitrary: T rule: widen1.induct) auto
qed

lemma widen1_is_type:
  assumes wfP: "wf_prog wfmd P"
  shows "(A, B) \<in> widen1 P \<Longrightarrow> is_type P B"
proof(induct rule: widen1.induct)
  case (widen1_Class C D)
  note CD = `P \<turnstile> C \<prec>\<^sup>1 D`
  hence "is_class P C"
    by(auto intro: subcls_is_class)
  with CD have "is_class P D"
    by(auto intro: converse_subcls_is_class[OF wfP])
  thus ?case by simp
next
  case (widen1_Array_Array T U)
  thus ?case by(cases U)(auto elim: widen1.cases)
qed(insert wfP, auto)

lemma widen1_trancl_is_type:
  assumes wfP: "wf_prog wfmd P"
  shows "(A, B) \<in> (widen1 P)^+ \<Longrightarrow> is_type P B"
apply(induct rule: trancl_induct)
apply(auto intro: widen1_is_type[OF wfP])
done

lemma single_valued_widen1:
  assumes wf: "wf_prog wf_md P"
  shows "single_valued (widen1 P)"
proof(rule single_valuedI)
  { fix x y z
    have "\<lbrakk> P \<turnstile> x <\<^sup>1 y; P \<turnstile> x <\<^sup>1 z \<rbrakk> \<Longrightarrow> y = z"
    proof(induct arbitrary: z rule: widen1.induct)
      case widen1_Class
      with single_valued_subcls1[OF wf] show ?case
	by(auto dest: single_valuedD elim!: widen1.cases)
    next
      case (widen1_Array_Array T U z)
      from `P \<turnstile> T\<lfloor>\<rceil> <\<^sup>1 z` `P \<turnstile> T <\<^sup>1 U` `\<not> is_NT_Array T`
      obtain z'
	where z': "z = z'\<lfloor>\<rceil>"
	and Tz': "P \<turnstile> T <\<^sup>1 z'"
	by(auto elim: widen1.cases)
      with `\<And>z. P \<turnstile> T <\<^sup>1 z \<Longrightarrow> U = z` have "U = z'" by blast
      with z' show ?case by simp
    qed(auto elim: widen1.cases) }
  thus "\<forall>x y. P \<turnstile> x <\<^sup>1 y \<longrightarrow> (\<forall>z. P \<turnstile> x <\<^sup>1 z \<longrightarrow> y = z)" by blast
qed

function class_numbering :: "'a prog \<Rightarrow> cname \<Rightarrow> nat" where
  "class_numbering P C =
   (if acyclicP (subcls1 P) \<and> is_class P C \<and> C \<noteq> Object
    then Suc (class_numbering P (fst (the (class P C))))
    else 0)"
by(pat_completeness, auto)
termination
proof(relation "{((P, C), (P', C')). P = P' \<and> acyclicP (subcls1 P) \<and> P \<turnstile> C' \<prec>\<^sup>1 C}")
  show "wf {((P, C), P', C'). P = P' \<and> acyclicP (subcls1 P) \<and> P \<turnstile> C' \<prec>\<^sup>1 C}"
  proof(rule wfUNIVI)
    fix Q x
    assume "\<forall>x. (\<forall>y. (y, x) \<in> {((P, C), P', C'). P = P' \<and> acyclicP (subcls1 P) \<and> P \<turnstile> C' \<prec>\<^sup>1 C} \<longrightarrow> Q y) \<longrightarrow> Q x"
    hence wf: "\<And>x. (\<And>y. (y, x) \<in> {((P, C), P', C'). P = P' \<and> acyclicP (subcls1 P) \<and> P \<turnstile> C' \<prec>\<^sup>1 C} \<Longrightarrow> Q y) \<Longrightarrow> Q x" by blast
    obtain P C where PC: "(x :: 'c prog \<times> cname) = (P, C)" by(cases x, auto)
    show "Q x"
    proof(cases "acyclicP (subcls1 P)")
      case False
      with PC show "Q x"
	by(auto intro: wf)
    next
      case True
      from True
      have wf'': "\<And>x. (\<And>y. (subcls1 P)\<inverse>\<inverse> y x \<Longrightarrow> Q (P, y)) \<Longrightarrow> Q (P, x)"
	by(auto intro: wf)
      show ?thesis
      proof(unfold PC, rule wf_induct[where P="\<lambda>C. Q (P, C)"])
	from True finite_subcls1'[of P] show "wf {(D, C). P \<turnstile> C \<prec>\<^sup>1 D}"
	  apply -
	  apply(erule finite_acyclic_wf)
	  apply(subst acyclic_converse[symmetric])
	  by(simp add: converse_def del: acyclic_converse)
      next
	fix x
	assume "\<forall>y. (y, x) \<in> {(D, C). P \<turnstile> C \<prec>\<^sup>1 D} \<longrightarrow> Q (P, y)"
	thus "Q (P, x)"
	  by(auto intro: wf'')
      qed
    qed
  qed
next
  fix P C
  assume "acyclicP (subcls1 P) \<and> is_class P C \<and> C \<noteq> Object"
  then obtain ac: "acyclicP (subcls1 P)"
    and ic: "is_class P C"
    and CObj: "C \<noteq> Object" by blast
  from ic CObj have "P \<turnstile> C \<prec>\<^sup>1 fst (the (class P C))"
    by(auto simp add: is_class_def intro: subcls1I)
  with ac show "((P, fst (the (class P C))), P, C) \<in> {((P, C), P', C'). P = P' \<and> acyclicP (subcls1 P) \<and> P \<turnstile> C' \<prec>\<^sup>1 C}"
    by(simp)
qed

fun wf_measure_widen1 :: "'a prog \<Rightarrow> ty \<Rightarrow> nat" where
  "wf_measure_widen1 P (Class C) = class_numbering P C"
| "wf_measure_widen1 P (Array T) = length (classes P) + wf_measure_widen1 P T"
| "wf_measure_widen1 P T = 0"

lemma wf_converse_widen1:
  assumes wfP: "wf_prog wfmc P"
  shows "wf ((widen1 P)^-1)"
proof(rule wf_subset)
  show "wf (measure (wf_measure_widen1 P))"
    by auto
next
  from wfP have lengthP: "length (classes P) > 0"
    by(cases P)(auto simp add: wf_prog_def wf_syscls_def is_class_def)
  { fix x y
    have "P \<turnstile> x <\<^sup>1 y \<Longrightarrow> wf_measure_widen1 P y < wf_measure_widen1 P x"
    proof(induct rule: widen1.induct)
      case (widen1_Class C D)
      note PCD = `P \<turnstile> C \<prec>\<^sup>1 D`
      from wfP have "acyclicP (subcls1 P)"
	by(rule acyclic_subcls1)
      moreover from PCD have "is_class P C" "C \<noteq> Object"
	by(auto elim: subcls1.cases simp: is_class_def)
      moreover from PCD obtain rest
	where "class P C = \<lfloor>(D, rest)\<rfloor>"
	by(auto elim!: subcls1.cases)
      ultimately show ?case 
	by(simp del: class_numbering.simps add: class_numbering.simps[where C=C])
    qed(insert lengthP, simp_all) }
  thus "(widen1 P)\<inverse> \<subseteq> measure (wf_measure_widen1 P)" by auto
qed

fun super :: "'a prog \<Rightarrow> ty \<Rightarrow> ty"
where
  "super P (Array Integer) = Class Object"
| "super P (Array Boolean) = Class Object"
| "super P (Array Void) = Class Object"
| "super P (Array (Class C)) = (if C = Object then Class Object else Array (super P (Class C)))"
| "super P (Array (Array T)) = Array (super P (Array T))"
| "super P (Class C) = Class (fst (the (class P C)))"

lemma superI:
  "P \<turnstile> T <\<^sup>1 U \<Longrightarrow> super P T = U"
proof(induct rule: widen1.induct)
  case (widen1_Array_Array T U)
  thus ?case by(cases T, auto elim: widen1.cases)
qed(auto dest: subcls1D)

lemma super_widen1:
  assumes icO: "is_class P Object"
  shows "P \<turnstile> T <\<^sup>1 U \<longleftrightarrow> is_type P T \<and> (case T of Class C  \<Rightarrow> (C \<noteq> Object \<and> U = super P T) 
                                              | Array T' \<Rightarrow> U = super P T 
                                              | _        \<Rightarrow> False)"
proof(induct T arbitrary: U)
  case (Class C' U')
  have "P \<turnstile> Class C' <\<^sup>1 U' \<longleftrightarrow> is_class P C' \<and> C' \<noteq> Object \<and> U' = super P (Class C')"
  proof(rule iffI)
    assume wd: "P \<turnstile> Class C' <\<^sup>1 U'"
    hence "is_type P (Class C')"
      by(auto elim!: widen1.cases intro: subcls_is_class)
    moreover from wd have "C' \<noteq> Object" by(auto)
    moreover from wd have "super P (Class C') = U'"
      by(rule superI)
    ultimately show "is_class P C' \<and> C' \<noteq> Object \<and> U' = super P (Class C')"
      by simp
  next
    assume "is_class P C' \<and> C' \<noteq> Object \<and> U' = super P (Class C')"
    then obtain "is_class P C'" "C' \<noteq> Object" "U' = super P (Class C')" by blast
    from `U' = super P (Class C')` obtain D where "U' = Class D" by(auto)
    moreover with `is_class P C'` `U' = super P (Class C')` `C' \<noteq> Object`
    have "P \<turnstile> C' \<prec>\<^sup>1 D" by(auto simp add: is_class_def intro!: subcls1.intros)
    hence "P \<turnstile> Class C' <\<^sup>1 Class D" by(rule widen1_Class)
    ultimately show "P \<turnstile> Class C' <\<^sup>1 U'" by simp
  qed
  thus ?case by simp
next
  case (Array T' U')
  note IH = this
  have "P \<turnstile> T'\<lfloor>\<rceil> <\<^sup>1 U' = (is_type P (T'\<lfloor>\<rceil>) \<and> U' = super P (T'\<lfloor>\<rceil>))"
  proof(rule iffI)
    assume wd: "P \<turnstile> T'\<lfloor>\<rceil> <\<^sup>1 U'"
    with icO have "is_type P (T'\<lfloor>\<rceil>)" by(rule is_type_widen1)
    moreover from wd have "super P (T'\<lfloor>\<rceil>) = U'" by(rule superI)
    ultimately show "is_type P (T'\<lfloor>\<rceil>) \<and> U' = super P (T'\<lfloor>\<rceil>)" by simp
  next
    assume "is_type P (T'\<lfloor>\<rceil>) \<and> U' = super P (T'\<lfloor>\<rceil>)"
    then obtain "is_type P (T'\<lfloor>\<rceil>)" and U': "U' = super P (T'\<lfloor>\<rceil>)" ..
    thus "P \<turnstile> T'\<lfloor>\<rceil> <\<^sup>1 U'"
    proof(cases T')
      case (Class D)
      show ?thesis
      proof(cases "D = Object")
	case True
	with Class U' icO
	show ?thesis by(auto intro: widen1_Array_Object)
      next
	case False
	with Class U' obtain D' where "U' = (Class D')\<lfloor>\<rceil>" by auto
	with U' Class False `is_type P (T'\<lfloor>\<rceil>)` have "P \<turnstile> D \<prec>\<^sup>1 D'"
	  by(auto simp add: is_class_def intro: subcls1.intros)
	hence "P \<turnstile> Class D <\<^sup>1 Class D'" by(rule widen1_Class)
	with `U' = (Class D')\<lfloor>\<rceil>` Class show ?thesis
	  by(auto intro: widen1_Array_Array)
      qed
    next
      case (Array V)
      with `is_type P (T'\<lfloor>\<rceil>)` have NT: "\<not> is_NT_Array V" by(simp split: ty.split_asm)
      with Array U' obtain V' where "U' = V'\<lfloor>\<rceil>" by(auto)
      with Array `is_type P (T'\<lfloor>\<rceil>)` U' NT  
      have "P \<turnstile> T' <\<^sup>1 V'" unfolding IH by(simp)
      with `U' = V'\<lfloor>\<rceil>` NT Array show ?thesis 
	by(auto intro: widen1_Array_Array)
    qed(auto intro: widen1.intros)
  qed    
  thus ?case by(simp)
qed(simp_all)

definition sup :: "'c prog \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> ty err" where
  "sup P T U \<equiv>
   if is_refT T \<and> is_refT U
   then OK (if U = NT then T
            else if T = NT then U
            else exec_lub (widen1 P) (super P) T U)
   else if (T = U) then OK T else Err"

lemma sup_def':
  "sup P = (\<lambda>T U.
   if is_refT T \<and> is_refT U
   then OK (if U = NT then T
            else if T = NT then U
            else exec_lub (widen1 P) (super P) T U)
   else if (T = U) then OK T else Err)"
  by (simp add: fun_eq_iff sup_def)

definition esl :: "'m prog \<Rightarrow> ty esl"
where
  "esl P = (types P, widen P, sup P)"



lemma order_widen [intro,simp]: 
  "wf_prog m P \<Longrightarrow> order (widen P)"
unfolding Semilat.order_def lesub_def
by (auto intro: widen_trans widen_antisym)



lemma subcls1_trancl_widen1_trancl:
  "(subcls1 P)^++ C D \<Longrightarrow> (Class C, Class D) \<in> (widen1 P)^+"
proof(induct rule: tranclp_induct[consumes 1, case_names base step])
  case base thus ?case
    by -(rule r_into_trancl, rule widen1.intros)
next
  case (step D E)
  from `P \<turnstile> D \<prec>\<^sup>1 E` have "(Class D, Class E) \<in> widen1 P"
    by(rule widen1.intros)
  with `(Class C, Class D) \<in> (widen1 P)\<^sup>+` show ?case
    by(rule trancl_into_trancl)
qed

lemma subcls_into_widen1_rtrancl:
  "P \<turnstile> C \<preceq>\<^sup>* D \<Longrightarrow> (Class C, Class D) \<in> (widen1 P)\<^sup>*"
by(induct rule: rtranclp.induct)(auto intro: rtrancl_refl widen1_Class elim: rtrancl_into_rtrancl)

lemma not_widen1_NT_Array:
  "\<lbrakk> P \<turnstile> U <\<^sup>1 T; is_NT_Array T \<rbrakk> \<Longrightarrow> False"
by(induct rule: widen1.induct)(auto)

lemma not_widen1_trancl_NT_Array:
  "\<lbrakk> (U, T) \<in> (widen1 P)^+; is_NT_Array T \<rbrakk> \<Longrightarrow> False"
by(induct rule: trancl.induct)(auto intro: not_widen1_NT_Array)

lemma widen1_trancl_into_Array_widen1_trancl:
  "\<lbrakk> (A, B) \<in> (widen1 P)\<^sup>+; \<not> is_NT_Array A \<rbrakk> \<Longrightarrow> (A\<lfloor>\<rceil>, B\<lfloor>\<rceil>) \<in> (widen1 P)\<^sup>+"
apply(induct rule: trancl.induct)
 apply(rule r_into_trancl)
 apply(erule widen1_Array_Array, assumption)
apply(clarsimp)
apply(case_tac "is_NT_Array b")
 apply(fastforce dest: not_widen1_trancl_NT_Array)
apply(auto dest: widen1_Array_Array)
done

lemma widen1_rtrancl_into_Array_widen1_rtrancl:
  "\<lbrakk> (A, B) \<in> (widen1 P)\<^sup>*; \<not> is_NT_Array A \<rbrakk> \<Longrightarrow> (A\<lfloor>\<rceil>, B\<lfloor>\<rceil>) \<in> (widen1 P)\<^sup>*"
apply(erule rtranclE)
 apply(simp)
apply(rule trancl_into_rtrancl)
apply(rule widen1_trancl_into_Array_widen1_trancl)
by(rule rtrancl_into_trancl1)

lemma Array_Object_widen1_trancl:
  assumes wf: "wf_prog wmdc P"
  and itA: "is_type P (A\<lfloor>\<rceil>)"
  shows "(A\<lfloor>\<rceil>, Class Object) \<in> (widen1 P)\<^sup>+"
using itA
proof(induct A)
  case (Class C)
  from `is_type P (Class C\<lfloor>\<rceil>)`
  have "is_class P C" by simp
  hence "P \<turnstile> C \<preceq>\<^sup>* Object"
    by(rule subcls_C_Object[OF _ wf])
  hence "(Class C, Class Object) \<in> (widen1 P)\<^sup>*"
    by(rule subcls_into_widen1_rtrancl)
  hence "(Class C\<lfloor>\<rceil>, Class Object\<lfloor>\<rceil>) \<in> (widen1 P)\<^sup>*"
    by(auto intro: widen1_rtrancl_into_Array_widen1_rtrancl)
  with widen1_Array_Object[where P=P] is_class_Object[OF wf] 
  show ?case by(blast intro: rtrancl_into_trancl1)
next
  case (Array A)
  note IH = `is_type P (A\<lfloor>\<rceil>) \<Longrightarrow> (A\<lfloor>\<rceil>, Class Object) \<in> (widen1 P)\<^sup>+`
  from `is_type P (A\<lfloor>\<rceil>\<lfloor>\<rceil>)` have "is_type P (A\<lfloor>\<rceil>)" by(rule is_type_ArrayD)
  hence "(A\<lfloor>\<rceil>, Class Object) \<in> (widen1 P)\<^sup>+" by(rule IH)
  hence "(A\<lfloor>\<rceil>, Class Object) \<in> (widen1 P)\<^sup>*"
    by(rule trancl_into_rtrancl)
  moreover from `is_type P (A\<lfloor>\<rceil>\<lfloor>\<rceil>)` have "\<not> is_NT_Array (A\<lfloor>\<rceil>)" by auto
  ultimately have "(A\<lfloor>\<rceil>\<lfloor>\<rceil>, Class Object\<lfloor>\<rceil>) \<in> (widen1 P)\<^sup>*"
    by(rule widen1_rtrancl_into_Array_widen1_rtrancl)
  with widen1_Array_Object[where P=P] is_class_Object[OF wf]
  show ?case by (blast intro: rtrancl_into_trancl1)
qed(auto intro: widen1.intros)

lemma widen_into_widen1_trancl:
  assumes wf: "wf_prog wfmd P"
  shows "\<lbrakk> P \<turnstile> A \<le> B; A \<noteq> B; A \<noteq> NT; is_type P A \<rbrakk> \<Longrightarrow> (A, B) \<in> (widen1 P)^+"
proof(induct rule: widen.induct)
  case (widen_subcls C D)
  from `Class C \<noteq> Class D` `P \<turnstile> C \<preceq>\<^sup>* D`
  have "(subcls1 P)\<^sup>+\<^sup>+ C D"
    by(auto elim: rtranclp.cases intro: rtranclp_into_tranclp1)
  thus ?case
    by(rule subcls1_trancl_widen1_trancl)
next
  case widen_array_object thus ?case by(auto intro: Array_Object_widen1_trancl[OF wf])
next
  case (widen_array_array A B)
  hence "(A, B) \<in> (widen1 P)\<^sup>+" by(cases A, auto)
  moreover from `is_type P (A\<lfloor>\<rceil>)` have "\<not> is_NT_Array A" by auto
  ultimately show "(A\<lfloor>\<rceil>, B\<lfloor>\<rceil>) \<in> (widen1 P)\<^sup>+"
    by(rule widen1_trancl_into_Array_widen1_trancl)
qed(fastforce)+

lemma wf_prog_impl_acc_widen:
  assumes wfP: "wf_prog wfmd P"
  shows "acc (types P) (widen P)"
proof -
  from wf_converse_widen1[OF wfP]
  have "wf (((widen1 P)^-1)^+)" by(rule wf_trancl)

  hence wfw1t: "\<And>M T. T \<in> M \<Longrightarrow> (\<exists>z\<in>M. \<forall>y. (y, z) \<in> ((widen1 P)\<inverse>)\<^sup>+ \<longrightarrow> y \<notin> M)"
    by(auto simp only: wf_eq_minimal)
  have "wf {(y, x). is_type P x \<and> is_type P y \<and> widen P x y \<and> x \<noteq> y}"
    unfolding wf_eq_minimal
  proof(intro strip)
    fix M and T :: ty
    assume TM: "T \<in> M"
    show "\<exists>z\<in>M. \<forall>y. (y, z) \<in> {(y, T). is_type P T \<and> is_type P y \<and> widen P T y \<and> T \<noteq> y} \<longrightarrow> y \<notin> M"
    proof(cases "(\<exists>C. Class C \<in> M \<and> is_class P C) \<or> (\<exists>U. U\<lfloor>\<rceil> \<in> M \<and> is_type P (U\<lfloor>\<rceil>))")
      case True
      have BNTthesis: "\<And>B. \<lbrakk> B \<in> (M \<inter> types P) - {NT} \<rbrakk> \<Longrightarrow> ?thesis"
      proof -
	fix B
	assume BM: "B \<in> M \<inter> types P - {NT}"
	from wfw1t[OF BM] obtain z
	  where zM: "z \<in> M"
	  and znnt: "z \<noteq> NT"
          and itz: "is_type P z"
	  and y: "\<And>y. (y, z) \<in> ((widen1 P)\<inverse>)\<^sup>+ \<Longrightarrow> y \<notin> M \<inter> types P - {NT}" by blast
	show "?thesis B"
	proof(rule bexI[OF _ zM], rule allI, rule impI)
	  fix y
	  assume "(y, z) \<in> {(y, T). is_type P T \<and> is_type P y \<and> widen P T y \<and> T \<noteq> y}"
	  hence Pzy: "P \<turnstile> z \<le> y" and zy: "z \<noteq> y" and "is_type P y" by auto
	  hence "(z, y) \<in> (widen1 P)^+" using znnt itz
	    by -(rule widen_into_widen1_trancl[OF wfP])
	  hence ynM: "y \<notin> M \<inter> types P - {NT}"
	    by -(rule y, simp add: trancl_converse)
          thus "y \<notin> M" using Pzy znnt `is_type P y` by auto
	qed
      qed
      from True show ?thesis by(fastforce intro: BNTthesis)
    next
      case False
      
      hence not_is_class: "\<And>C. Class C \<in> M \<Longrightarrow> \<not> is_class P C"
        and not_is_array: "\<And>U. U\<lfloor>\<rceil> \<in> M \<Longrightarrow> \<not> is_type P (U\<lfloor>\<rceil>)" by simp_all

      show ?thesis
      proof(cases "\<exists>C. Class C \<in> M")
        case True
        then obtain C where "Class C \<in> M" ..
        with not_is_class[of C] show ?thesis
          by(blast dest: rtranclpD subcls_is_class Class_widen)
      next
        case False
        show ?thesis
        proof(cases "\<exists>T. Array T \<in> M")
          case True
          then obtain U where U: "Array U \<in> M" ..
          hence "\<not> is_type P (U\<lfloor>\<rceil>)" by(rule not_is_array)
          thus ?thesis using U by(auto simp del: is_type.simps)
        next
          case False
          with `\<not> (\<exists>C. Class C \<in> M)` TM
          have "\<forall>y. P \<turnstile> T \<le> y \<and> T \<noteq> y \<longrightarrow> y \<notin> M"
            by(cases T)(fastforce simp add: NT_widen)+
          thus ?thesis using TM by blast
        qed
      qed
    qed
  qed
  thus ?thesis by(simp add: Semilat.acc_def lesssub_def lesub_def)
qed

lemmas wf_widen_acc = wf_prog_impl_acc_widen
declare wf_widen_acc [intro, simp]

lemma acyclic_widen1:
  "wf_prog wfmc P \<Longrightarrow> acyclic (widen1 P)"
by(auto dest: wf_converse_widen1 wf_acyclic simp add: acyclic_converse)

lemma widen1_into_widen:
  assumes wf: "wf_prog wf_mb P"
  shows "(A, B) \<in> widen1 P \<Longrightarrow> P \<turnstile> A \<le> B"
apply(induct rule: widen1.induct)
apply(insert is_class_Object[OF wf])
apply(auto intro: widen.intros elim: widen1.cases)
done

lemma widen1_rtrancl_into_widen:
  assumes wf: "wf_prog wf_mb P"
  shows "(A, B) \<in> (widen1 P)^* \<Longrightarrow> P \<turnstile> A \<le> B"
apply(induct rule: rtrancl_induct)
apply(insert wf)
by(auto dest!: widen1_into_widen elim: widen_trans)

lemma widen_eq_widen1_trancl:
  "\<lbrakk> wf_prog wf_md P; T \<noteq> NT; T \<noteq> U; is_type P T \<rbrakk> \<Longrightarrow> P \<turnstile> T \<le> U \<longleftrightarrow> P \<turnstile> T <\<^sup>+ U"
apply(rule iffI)
 apply(rule widen_into_widen1_trancl, assumption+)
apply(erule widen1_rtrancl_into_widen)
by(rule trancl_into_rtrancl)

lemma sup_is_type:
  assumes wf: "wf_prog wf_md P"
  and itA: "is_type P A"
  and itB: "is_type P B"
  and sup: "sup P A B = OK T"
  shows "is_type P T"
proof -
  { assume ANT: "A \<noteq> NT"
      and BNT: "B \<noteq> NT"
      and AnB: "A \<noteq> B"
      and RTA: "is_refT A"
      and RTB: "is_refT B"
    with itA itB have AObject: "P \<turnstile> A \<le> Class Object"
      and BObject: "P \<turnstile> B \<le> Class Object"
      by(auto intro: is_refType_widen_Object[OF wf])
    have "is_type P (exec_lub (widen1 P) (super P) A B)"
    proof(cases "A = Class Object \<or> B = Class Object")
      case True
      hence "exec_lub (widen1 P) (super P) A B = Class Object"
      proof(rule disjE)
	assume A: "A = Class Object"
	moreover
	from BObject BNT itB
	have "(B, Class Object) \<in> (widen1 P)\<^sup>*"
	  by(cases "B = Class Object", auto intro: trancl_into_rtrancl widen_into_widen1_trancl[OF wf])
	hence "is_ub ((widen1 P)\<^sup>*) (Class Object) B (Class Object)"
	  by(auto intro: is_ubI)
	hence "is_lub ((widen1 P)\<^sup>*) (Class Object) B (Class Object)"
	  by(auto simp add: is_lub_def dest: is_ubD)
	with acyclic_widen1[OF wf]
	have "exec_lub (widen1 P) (super P) (Class Object) B = Class Object"
	  by(auto intro: exec_lub_conv superI)
	ultimately show "exec_lub (widen1 P) (super P) A B = Class Object" by simp
      next
	assume B: "B = Class Object"
	moreover
	from AObject ANT itA
	have "(A, Class Object) \<in> (widen1 P)\<^sup>*"
	  by(cases "A = Class Object", auto intro: trancl_into_rtrancl widen_into_widen1_trancl[OF wf])
	hence "is_ub ((widen1 P)\<^sup>*) (Class Object) A (Class Object)"
	  by(auto intro: is_ubI)
	hence "is_lub ((widen1 P)\<^sup>*) (Class Object) A (Class Object)"
	  by(auto simp add: is_lub_def dest: is_ubD)
	with acyclic_widen1[OF wf]
	have "exec_lub (widen1 P) (super P) A (Class Object) = Class Object"
	  by(auto intro: exec_lub_conv superI)
	ultimately show "exec_lub (widen1 P) (super P) A B = Class Object" by simp
      qed
      with wf show ?thesis by(simp)
    next
      case False
      hence AnObject: "A \<noteq> Class Object"
	and BnObject: "B \<noteq> Class Object" by auto
      from widen_into_widen1_trancl[OF wf AObject AnObject ANT itA]
      have "(A, Class Object) \<in> (widen1 P)\<^sup>*"
	by(rule trancl_into_rtrancl)
      moreover from widen_into_widen1_trancl[OF wf BObject BnObject BNT itB]
      have "(B, Class Object) \<in> (widen1 P)\<^sup>*"
	by(rule trancl_into_rtrancl)
      ultimately have "is_lub ((widen1 P)\<^sup>*) A B (exec_lub (widen1 P) (super P) A B)"
	by(rule is_lub_exec_lub[OF single_valued_widen1[OF wf] acyclic_widen1[OF wf]])(auto intro: superI)
      hence Aew1: "(A, exec_lub (widen1 P) (super P) A B) \<in> (widen1 P)\<^sup>*"
	by(auto simp add: is_lub_def dest!: is_ubD)
      thus ?thesis
      proof(rule rtranclE)
	assume "A = exec_lub (widen1 P) (super P) A B"
	with itA show ?thesis by simp
      next
	fix A'
	assume "P \<turnstile> A' <\<^sup>1 exec_lub (widen1 P) (super P) A B"
	thus ?thesis by(rule widen1_is_type[OF wf])
      qed
    qed }
  with is_class_Object[OF wf] sup itA itB show ?thesis unfolding sup_def
    by(cases "A = B")(auto split: split_if_asm simp add: mem_def exec_lub_refl)
qed

lemma closed_err_types:
  assumes wfP: "wf_prog wf_mb P"
  shows "closed (err (types P)) (lift2 (sup P))"
proof -
  { fix A B
    assume it: "is_type P A" "is_type P B"
      and "A \<noteq> NT" "B \<noteq> NT" "A \<noteq> B"
      and "is_refT A" "is_refT B"
    hence "is_type P (exec_lub (widen1 P) (super P) A B)"
      using sup_is_type[OF wfP it] by(simp add: sup_def) }
  with is_class_Object[OF wfP] show ?thesis
    unfolding closed_def plussub_def lift2_def sup_def'
    by(auto split: err.split ty.splits)(auto simp add: exec_lub_refl)
qed

lemma widen_into_widen1_rtrancl:
  "\<lbrakk>wf_prog wfmd P; widen P A B; A \<noteq> NT; is_type P A \<rbrakk> \<Longrightarrow> (A, B) \<in> (widen1 P)\<^sup>*"
apply(cases "A = B", auto intro: trancl_into_rtrancl widen_into_widen1_trancl)
done


lemma sup_widen_greater:
  assumes wfP: "wf_prog wf_mb P"
  and it1: "is_type P t1"
  and it2: "is_type P t2"
  and sup: "sup P t1 t2 = OK s"
  shows "widen P t1 s \<and> widen P t2 s"
proof -
  have "\<lbrakk> is_refT t1; is_refT t2; t1 \<noteq> NT; t2 \<noteq> NT \<rbrakk>
    \<Longrightarrow> P \<turnstile> t1 \<le> exec_lub (widen1 P) (super P) t1 t2
     \<and> P \<turnstile> t2 \<le> exec_lub (widen1 P) (super P) t1 t2"
  proof -
    assume t1: "is_refT t1"
      and t2: "is_refT t2"
      and t1NT: "t1 \<noteq> NT"
      and t2NT: "t2 \<noteq> NT"
    with it1 it2 wfP have "P \<turnstile> t1 \<le> Class Object" "P \<turnstile> t2 \<le> Class Object"
      by(auto intro: is_refType_widen_Object)
    with t1NT t2NT it1 it2
    have "(t1, Class Object) \<in> (widen1 P)^*" "(t2, Class Object) \<in> (widen1 P)^*"
      by(auto intro: widen_into_widen1_rtrancl[OF wfP])
    with single_valued_widen1[OF wfP]
    obtain u where
      "is_lub ((widen1 P)^* ) t1 t2 u" 
      by (blast dest: single_valued_has_lubs)
    moreover
    note acyclic_widen1[OF wfP]
    moreover
    have "\<forall>x y. (x, y) \<in> widen1 P \<longrightarrow> super P x = y"
      by (blast intro: superI)
    ultimately
    show "P \<turnstile> t1 \<le> exec_lub (widen1 P) (super P) t1 t2 \<and>
          P \<turnstile> t2 \<le> exec_lub (widen1 P) (super P) t1 t2"
      by (simp add: exec_lub_conv) (blast dest: is_lubD is_ubD intro: widen1_rtrancl_into_widen[OF wfP])
  qed
  with it1 it2 sup show ?thesis
    by(cases s, auto simp add: sup_def split: split_if_asm elim: refTE)
qed

lemma sup_widen_smallest:
  assumes wfP: "wf_prog wf_mb P"
  and itT: "is_type P T"
  and itU: "is_type P U"
  and TwV: "P \<turnstile> T \<le> V"
  and UwV: "P \<turnstile> U \<le> V"
  and sup: "sup P T U = OK W"
  shows "widen P W V"
proof -
  { assume rT: "is_refT T"
      and rU: "is_refT U"
      and UNT: "U \<noteq> NT"
      and TNT: "T \<noteq> NT"
      and W: "exec_lub (widen1 P) (super P) T U = W"
    from itU itT rT rU UNT TNT have "P \<turnstile> T \<le> Class Object" "P \<turnstile> U \<le> Class Object"
      by(auto intro:is_refType_widen_Object[OF wfP])
    with UNT TNT itT itU
    have "(T, Class Object) \<in> (widen1 P)^*" "(U, Class Object) \<in> (widen1 P)^*"
      by(auto intro: widen_into_widen1_rtrancl[OF wfP])
    with single_valued_widen1[OF wfP]
    obtain X where
      lub: "is_lub ((widen1 P)^* ) T U X"
      by (blast dest: single_valued_has_lubs)   
    with acyclic_widen1[OF wfP]
    have "exec_lub (widen1 P) (super P) T U = X"
      by (blast intro: superI exec_lub_conv)
    moreover
    from TwV TNT UwV UNT itT itU have "(T, V) \<in> (widen1 P)^*" "(U, V) \<in> (widen1 P)^*"
      by(auto intro: widen_into_widen1_rtrancl[OF wfP])
    with lub have "(X, V) \<in> (widen1 P)^*" 
      by (clarsimp simp add: is_lub_def is_ub_def)
    ultimately
    have "(exec_lub (widen1 P) (super P) T U, V) \<in> (widen1 P)^*"
      by blast
    hence "P \<turnstile> exec_lub (widen1 P) (super P) T U \<le> V"
      by(rule widen1_rtrancl_into_widen[OF wfP])
    with W have "P \<turnstile> W \<le> V" by simp }
  with sup itT itU TwV UwV show ?thesis
    by(simp add: sup_def split: split_if_asm)
qed

lemma sup_exists:
  "\<lbrakk> widen P a c; widen P b c \<rbrakk> \<Longrightarrow> EX T. sup P a b = OK T"
(*<*)
apply (unfold sup_def)
apply (cases b)
apply auto
apply (cases a)
apply auto
apply (cases a)
apply auto
apply(cases a)
apply(auto)
done
(*>*)

lemma err_semilat_JType_esl:
  "wf_prog wf_mb P \<Longrightarrow> err_semilat (esl P)"
proof -
  assume wf_prog: "wf_prog wf_mb P"  
  hence "order (widen P)"..
  moreover from wf_prog
  have "closed (err (types P)) (lift2 (sup P))"
    by (rule closed_err_types)
  moreover
  from wf_prog have
    "(\<forall>x\<in>err (types P). \<forall>y\<in>err (types P). x \<sqsubseteq>\<^bsub>Err.le (widen P)\<^esub> x \<squnion>\<^bsub>lift2 (sup P)\<^esub> y) \<and> 
     (\<forall>x\<in>err (types P). \<forall>y\<in>err (types P). y \<sqsubseteq>\<^bsub>Err.le (widen P)\<^esub> x \<squnion>\<^bsub>lift2 (sup P)\<^esub> y)"
    by(auto simp add: lesub_def plussub_def Err.le_def lift2_def sup_widen_greater split: err.split)
  moreover from wf_prog have
    "\<forall>x\<in>err (types P). \<forall>y\<in>err (types P). \<forall>z\<in>err (types P). 
    x \<sqsubseteq>\<^bsub>Err.le (widen P)\<^esub> z \<and> y \<sqsubseteq>\<^bsub>Err.le (widen P)\<^esub> z \<longrightarrow> x \<squnion>\<^bsub>lift2 (sup P)\<^esub> y \<sqsubseteq>\<^bsub>Err.le (widen P)\<^esub> z"
    by (unfold lift2_def plussub_def lesub_def Err.le_def)
       (auto intro: sup_widen_smallest dest:sup_exists simp add: split: err.split)
  ultimately show ?thesis by (simp add: esl_def semilat_def sl_def Err.sl_def)
qed

subsection {* Relation between @{term "sup P T U = OK V"} and @{term "P \<turnstile> lub(T, U) = V"} *}

lemma sup_is_lubI:
  assumes wf: "wf_prog wf_md P"
  and it: "is_type P T" "is_type P U"
  and sup: "sup P T U = OK V"
  shows "P \<turnstile> lub(T, U) = V"
proof 
  from sup_widen_greater[OF wf it sup]
  show "P \<turnstile> T \<le> V" "P \<turnstile> U \<le> V" by blast+
next
  fix T'
  assume "P \<turnstile> T \<le> T'" "P \<turnstile> U \<le> T'"
  with wf it show "P \<turnstile> V \<le> T'" using sup by(rule sup_widen_smallest)
qed

lemma is_lub_subD:
  assumes wf: "wf_prog wf_md P"
  and it: "is_type P T" "is_type P U"
  and lub: "P \<turnstile> lub(T, U) = V"
  shows "sup P T U = OK V"
proof -
  from lub have "P \<turnstile> T \<le> V" "P \<turnstile> U \<le> V" by(blast dest: is_lub_upper)+
  from sup_exists[OF this] obtain W where "sup P T U = OK W" by blast
  moreover
  with wf it have "P \<turnstile> lub(T, U) = W" by(rule sup_is_lubI)
  with lub have "V = W" by(auto dest: is_lub_unique[OF wf])
  ultimately show ?thesis by simp
qed

lemma is_lub_is_type:
  "\<lbrakk> wf_prog wf_md P; is_type P T; is_type P U; P \<turnstile> lub(T, U) = V \<rbrakk> \<Longrightarrow> is_type P V"
by(frule (3) is_lub_subD)(erule (3) sup_is_type)

subsection {* Code generator setup *}

code_pred widen1p .
lemmas [code] = widen1_def

lemma eval_widen1p_i_i_o_conv:
  "Predicate.eval (widen1p_i_i_o P T) = (\<lambda>U. P \<turnstile> T <\<^sup>1 U)"
by(auto elim: widen1p_i_i_oE intro: widen1p_i_i_oI simp add: widen1_def fun_eq_iff)

lemma rtrancl_widen1_code [code_unfold]:
  "(widen1 P)^* = (\<lambda>(a, b). Predicate.holds (rtrancl_tab_FioB_i_i_i (widen1p_i_i_o P) [] a b))"
by(auto simp add: fun_eq_iff Predicate.holds_eq widen1_def Collect_def rtrancl_def mem_def rtranclp_eq_rtrancl_tab_nil eval_widen1p_i_i_o_conv intro!: rtrancl_tab_FioB_i_i_iI elim!: rtrancl_tab_FioB_i_i_iE)

declare exec_lub_def [code_unfold]

end
