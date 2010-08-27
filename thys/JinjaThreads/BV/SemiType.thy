(*  Title:      JinjaThreads/BV/SemiType.thy
    Author:     Tobias Nipkow, Gerwin Klein, Andreas Lochbihler
*)

header {* 
  \chapter{Bytecode verifier}
  \isaheader{The Jinja Type System as a Semilattice} 
*}

theory SemiType
imports "../Common/WellForm" "../../Jinja/DFA/Semilattices"
begin

inductive_set
  widen1 :: "'a prog \<Rightarrow> (ty \<times> ty) set"
  and widen1_syntax :: "'a prog \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool" ("_ \<turnstile> _ <\<^sup>1 _" [71,71,71] 70)
  for P :: "'a prog"
where
  "P \<turnstile> C <\<^sup>1 D \<equiv> (C, D) \<in> widen1 P"

| widen1_Array_Object:
  "(* is_class P Object \<Longrightarrow> *) P \<turnstile> Array (Class Object) <\<^sup>1 Class Object"

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

| widen1_NT_Object:
  "is_NT_Array T \<Longrightarrow> P \<turnstile> Array T <\<^sup>1 Class Object"

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
apply(induct rule: widen1.induct)
apply(auto intro: subcls_is_class NT_Array_is_type icO)
done


lemma widen1_NT_Array:
  assumes NT: "is_NT_Array T"
  shows "P \<turnstile> T\<lfloor>\<rceil> <\<^sup>1 U \<longleftrightarrow> U = Class Object"
proof(rule iffI)
  assume "P \<turnstile> T\<lfloor>\<rceil> <\<^sup>1 U"
  moreover
  { fix T'
    have "\<lbrakk> P \<turnstile> T' <\<^sup>1 U; T' = T\<lfloor>\<rceil>; is_NT_Array T' \<rbrakk> \<Longrightarrow> U = Class Object"
      by(induct arbitrary: T rule: widen1.induct, auto) }
  ultimately show "U = Class Object" using NT by auto
next
  assume "U = Class Object"
  with NT show "P \<turnstile> T\<lfloor>\<rceil> <\<^sup>1 U"
    by(auto intro: widen1_NT_Object)
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
qed(insert wfP, auto intro: NT_Array_is_type)

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
| "wf_measure_widen1 P (Array T) = length P + wf_measure_widen1 P T"
| "wf_measure_widen1 P T = 0"

lemma wf_converse_widen1:
  assumes wfP: "wf_prog wfmc P"
  shows "wf ((widen1 P)^-1)"
proof(rule wf_subset)
  show "wf (measure (wf_measure_widen1 P))"
    by auto
next
  from wfP have lengthP: "length P > 0"
    by(auto simp add: wf_prog_def wf_syscls_def)
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
| "super P (Array NT) = Class Object"
| "super P (Array (Array T)) = (if is_NT_Array T then Class Object else Array (super P (Array T)))"
| "super P (Class C) = Class (fst (the (class P C)))"

lemma superI:
  "P \<turnstile> T <\<^sup>1 U \<Longrightarrow> super P T = U"
proof(induct rule: widen1.induct)
  case (widen1_Array_Array T U)
  thus ?case by(cases T, auto elim: widen1.cases)
next
  case (widen1_NT_Object T)
  thus ?case by(cases T, auto)
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
  have "P \<turnstile> T'\<lfloor>\<rceil> <\<^sup>1 U' = (is_type P T' \<and> U' = super P (T'\<lfloor>\<rceil>))"
  proof(rule iffI)
    assume wd: "P \<turnstile> T'\<lfloor>\<rceil> <\<^sup>1 U'"
    hence "is_type P T'" using icO
      by(auto dest: is_type_widen1)
    moreover from wd have "super P (T'\<lfloor>\<rceil>) = U'" by(rule superI)
    ultimately show "is_type P T' \<and> U' = super P (T'\<lfloor>\<rceil>)" by simp
  next
    assume "is_type P T' \<and> U' = super P (T'\<lfloor>\<rceil>)"
    then obtain "is_type P T'"
      and U': "U' = super P (T'\<lfloor>\<rceil>)" by blast
    from U' show "P \<turnstile> T'\<lfloor>\<rceil> <\<^sup>1 U'"
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
	with U' Class False `is_type P T'` have "P \<turnstile> D \<prec>\<^sup>1 D'"
	  by(auto simp add: is_class_def intro: subcls1.intros)
	hence "P \<turnstile> Class D <\<^sup>1 Class D'" by(rule widen1_Class)
	with `U' = (Class D')\<lfloor>\<rceil>` Class show ?thesis
	  by(auto intro: widen1_Array_Array)
      qed
    next
      case (Array V)
      show ?thesis
      proof(cases "is_NT_Array V")
	case True
	with Array U' have "U' = Class Object" by(simp)
	with True Array show ?thesis by(auto intro: widen1_NT_Object)
      next
	case False
	with Array U' obtain V' where "U' = V'\<lfloor>\<rceil>" by(auto)
	with Array `is_type P T'` U' False 
	have "P \<turnstile> T' <\<^sup>1 V'"
	  unfolding `\<And>U. P \<turnstile> T' <\<^sup>1 U = (is_type P T' \<and> (case T' of Class C \<Rightarrow> C \<noteq> Object \<and> U = super P T' | T\<lfloor>\<rceil> \<Rightarrow> U = super P T' | _ \<Rightarrow> False))`
	  by(simp)
	with `U' = V'\<lfloor>\<rceil>` False Array show ?thesis 
	  by(auto intro: widen1_Array_Array)
      qed
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

definition esl :: "'c prog \<Rightarrow> ty esl" where
  "esl P \<equiv> (is_type P, widen P, sup P)"



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
 apply(fastsimp dest: not_widen1_trancl_NT_Array)
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
  and itA: "is_type P A"
  shows "(A\<lfloor>\<rceil>, Class Object) \<in> (widen1 P)\<^sup>+"
proof(cases "is_NT_Array A")
  case True thus ?thesis
    by(auto intro: r_into_trancl widen1_NT_Object)
next
  case False
  show ?thesis using itA False
  proof(induct A)
    case (Class C)
    from `is_type P (Class C)`
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
    note IH = `\<lbrakk> is_type P A; \<not> is_NT_Array A \<rbrakk> \<Longrightarrow> (A\<lfloor>\<rceil>, Class Object) \<in> (widen1 P)\<^sup>+`
    from `is_type P (A\<lfloor>\<rceil>)` `\<not> is_NT_Array (A\<lfloor>\<rceil>)`
    have "(A\<lfloor>\<rceil>, Class Object) \<in> (widen1 P)\<^sup>+"
      by(auto intro: IH)
    hence "(A\<lfloor>\<rceil>, Class Object) \<in> (widen1 P)\<^sup>*"
      by(rule trancl_into_rtrancl)
    hence "(A\<lfloor>\<rceil>\<lfloor>\<rceil>, Class Object\<lfloor>\<rceil>) \<in> (widen1 P)\<^sup>*" using `\<not> is_NT_Array (A\<lfloor>\<rceil>)`
      by(rule widen1_rtrancl_into_Array_widen1_rtrancl)
    with widen1_Array_Object[where P=P] is_class_Object[OF wf]
    show ?case by (blast intro: rtrancl_into_trancl1)
  qed(auto intro: widen1.intros)
qed

lemma widen_into_widen1_trancl:
  assumes wf: "wf_prog wfmd P"
  shows "\<lbrakk> P \<turnstile> A \<le> B; A \<noteq> B; A \<noteq> NT \<rbrakk> \<Longrightarrow> (A, B) \<in> (widen1 P)^+"
proof(induct rule: widen.induct)
  case (widen_subcls C D)
  from `Class C \<noteq> Class D` `P \<turnstile> C \<preceq>\<^sup>* D`
  have "(subcls1 P)\<^sup>+\<^sup>+ C D"
    by(auto elim: rtranclp.cases intro: rtranclp_into_tranclp1)
  thus ?case
    by(rule subcls1_trancl_widen1_trancl)
next
  case (widen_array_object A)
  thus ?case
    by - (rule Array_Object_widen1_trancl[OF wf])
next
  case (widen_array_array A B)
  hence "(A, B) \<in> (widen1 P)\<^sup>+" by(cases A, auto)
  with `\<not> is_NT_Array A` show "(A\<lfloor>\<rceil>, B\<lfloor>\<rceil>) \<in> (widen1 P)\<^sup>+"
    by -(rule widen1_trancl_into_Array_widen1_trancl)
qed(fastsimp)+


lemma wf_prog_impl_acc_widen:
  assumes wfP: "wf_prog wfmd P"
  shows "acc (widen P)"
proof -
  from wf_converse_widen1[OF wfP]
  have "wf (((widen1 P)^-1)^+)"
    by(rule wf_trancl)
  hence wfw1t: "\<And>M T. T \<in> M \<Longrightarrow> (\<exists>z\<in>M. \<forall>y. (y, z) \<in> ((widen1 P)\<inverse>)\<^sup>+ \<longrightarrow> y \<notin> M)"
    by(auto simp only: wf_eq_minimal)
  { fix M T
    assume TM: "(T :: ty) \<in> M"
    have "\<exists>z\<in>M. \<forall>y. (y, z) \<in> {(y, T). widen P T y \<and> T \<noteq> y} \<longrightarrow> y \<notin> M"
    proof(cases "(\<exists>C. Class C \<in> M) \<or> (\<exists>U. U\<lfloor>\<rceil> \<in> M)")
      case False
      thus ?thesis
	by -(rule bexI[OF _ TM], cases T, auto simp: NT_widen Class_widen2 dest: Array_widen)
    next
      case True
      have BNTthesis: "\<And>B. B \<in> M - {NT} \<Longrightarrow> ?thesis"
      proof -
	fix B
	assume BM: "B \<in> M - {NT}"
	from wfw1t[OF BM] obtain z
	  where zM: "z \<in> M"
	  and znnt: "z \<noteq> NT"
	  and y: "\<And>y. (y, z) \<in> ((widen1 P)\<inverse>)\<^sup>+ \<Longrightarrow> y \<notin> M - {NT}" by blast
	show "?thesis B"
	proof(rule bexI[OF _ zM], rule allI, rule impI)
	  fix y
	  assume "(y, z) \<in> {(y, T). widen P T y \<and> T \<noteq> y}"
	  hence Pzy: "P \<turnstile> z \<le> y" and zy: "z \<noteq> y" by auto
	  hence "(z, y) \<in> (widen1 P)^+" using znnt
	    by(rule widen_into_widen1_trancl[OF wfP])
	  hence ynM: "y \<notin> M - {NT}"
	    by -(rule y, simp add: trancl_converse)
	  with Pzy znnt show "y \<notin> M" by(auto)
	qed
      qed
      from True show ?thesis
	by -(erule disjE, (erule exE, rule BNTthesis, fastsimp)+)
    qed }
  hence "wf {(y, x). widen P x y \<and> x \<noteq> y}"
    by(clarsimp simp only: wf_eq_minimal)
  thus ?thesis
    by(unfold Semilat.acc_def lesssub_def lesub_def)
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
apply(auto intro: widen.intros NT_Array_is_type elim: widen1.cases)
done

lemma widen1_rtrancl_into_widen:
  assumes wf: "wf_prog wf_mb P"
  shows "(A, B) \<in> (widen1 P)^* \<Longrightarrow> P \<turnstile> A \<le> B"
apply(induct rule: rtrancl_induct)
apply(insert wf)
by(auto dest!: widen1_into_widen elim: widen_trans)

lemma widen_eq_widen1_trancl:
  "\<lbrakk> wf_prog wf_md P; T \<noteq> NT; T \<noteq> U \<rbrakk> \<Longrightarrow> P \<turnstile> T \<le> U \<longleftrightarrow> P \<turnstile> T <\<^sup>+ U"
apply(rule iffI)
 apply(rule widen_into_widen1_trancl, assumption+)
apply(erule widen1_rtrancl_into_widen)
by(rule trancl_into_rtrancl)

lemma closed_err_types:
  assumes wfP: "wf_prog wf_mb P"
  shows "closed (err (is_type P)) (lift2 (sup P))"
proof -
  { fix A B
    assume itA: "is_type P A"
      and itB: "is_type P B"
      and ANT: "A \<noteq> NT"
      and BNT: "B \<noteq> NT"
      and AnB: "A \<noteq> B"
      and RTA: "is_refT A"
      and RTB: "is_refT B"
    hence AObject: "P \<turnstile> A \<le> Class Object"
      and BObject: "P \<turnstile> B \<le> Class Object"
      by(auto intro: is_refType_widen_Object[OF wfP])
    have "is_type P (exec_lub (widen1 P) (super P) A B)"
    proof(cases "A = Class Object \<or> B = Class Object")
      case True
      hence "exec_lub (widen1 P) (super P) A B = Class Object"
      proof(rule disjE)
	assume A: "A = Class Object"
	moreover
	from BObject BNT
	have "(B, Class Object) \<in> (widen1 P)\<^sup>*"
	  by(cases "B = Class Object", auto intro: trancl_into_rtrancl widen_into_widen1_trancl[OF wfP])
	hence "is_ub ((widen1 P)\<^sup>*) (Class Object) B (Class Object)"
	  by(auto intro: is_ubI)
	hence "is_lub ((widen1 P)\<^sup>*) (Class Object) B (Class Object)"
	  by(auto simp add: is_lub_def dest: is_ubD)
	with acyclic_widen1[OF wfP]
	have "exec_lub (widen1 P) (super P) (Class Object) B = Class Object"
	  by(auto intro: exec_lub_conv superI)
	ultimately show "exec_lub (widen1 P) (super P) A B = Class Object" by simp
      next
	assume B: "B = Class Object"
	moreover
	from AObject ANT
	have "(A, Class Object) \<in> (widen1 P)\<^sup>*"
	  by(cases "A = Class Object", auto intro: trancl_into_rtrancl widen_into_widen1_trancl[OF wfP])
	hence "is_ub ((widen1 P)\<^sup>*) (Class Object) A (Class Object)"
	  by(auto intro: is_ubI)
	hence "is_lub ((widen1 P)\<^sup>*) (Class Object) A (Class Object)"
	  by(auto simp add: is_lub_def dest: is_ubD)
	with acyclic_widen1[OF wfP]
	have "exec_lub (widen1 P) (super P) A (Class Object) = Class Object"
	  by(auto intro: exec_lub_conv superI)
	ultimately show "exec_lub (widen1 P) (super P) A B = Class Object" by simp
      qed
      with wfP show ?thesis by(simp)
    next
      case False
      hence AnObject: "A \<noteq> Class Object"
	and BnObject: "B \<noteq> Class Object" by auto
      from widen_into_widen1_trancl[OF wfP AObject AnObject ANT]
      have "(A, Class Object) \<in> (widen1 P)\<^sup>*"
	by(rule trancl_into_rtrancl)
      moreover from widen_into_widen1_trancl[OF wfP BObject BnObject BNT]
      have "(B, Class Object) \<in> (widen1 P)\<^sup>*"
	by(rule trancl_into_rtrancl)
      ultimately have "is_lub ((widen1 P)\<^sup>*) A B (exec_lub (widen1 P) (super P) A B)"
	apply(rule is_lub_exec_lub[OF single_valued_widen1[OF wfP] acyclic_widen1[OF wfP]])
	by(auto intro: superI)
      hence Aew1: "(A, exec_lub (widen1 P) (super P) A B) \<in> (widen1 P)\<^sup>*"
	by(auto simp add: is_lub_def dest!: is_ubD)
      thus ?thesis
      proof(rule rtranclE)
	assume "A = exec_lub (widen1 P) (super P) A B"
	with itA show ?thesis by simp
      next
	fix A'
	assume "P \<turnstile> A' <\<^sup>1 exec_lub (widen1 P) (super P) A B"
	thus ?thesis by(rule widen1_is_type[OF wfP])
      qed
    qed }
  with is_class_Object[OF wfP] show ?thesis
    unfolding closed_def plussub_def lift2_def sup_def
    by(auto split: err.split ty.splits)(auto simp add: mem_def exec_lub_refl)
qed

lemma widen_into_widen1_rtrancl:
  "\<lbrakk>wf_prog wfmd P; widen P A B; A \<noteq> NT\<rbrakk> \<Longrightarrow> (A, B) \<in> (widen1 P)\<^sup>*"
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
    with t1NT t2NT have "(t1, Class Object) \<in> (widen1 P)^*" "(t2, Class Object) \<in> (widen1 P)^*"
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
  and itV: "is_type P V"
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
    with UNT TNT have "(T, Class Object) \<in> (widen1 P)^*" "(U, Class Object) \<in> (widen1 P)^*"
      by(auto intro: widen_into_widen1_rtrancl[OF wfP])
    with single_valued_widen1[OF wfP]
    obtain X where
      lub: "is_lub ((widen1 P)^* ) T U X"
      by (blast dest: single_valued_has_lubs)   
    with acyclic_widen1[OF wfP]
    have "exec_lub (widen1 P) (super P) T U = X"
      by (blast intro: superI exec_lub_conv)
    moreover
    from TwV TNT UwV UNT have "(T, V) \<in> (widen1 P)^*" "(U, V) \<in> (widen1 P)^*"
      by(auto intro: widen_into_widen1_rtrancl[OF wfP])
    with lub have "(X, V) \<in> (widen1 P)^*" 
      by (clarsimp simp add: is_lub_def is_ub_def)
    ultimately
    have "(exec_lub (widen1 P) (super P) T U, V) \<in> (widen1 P)^*"
      by blast
    hence "P \<turnstile> exec_lub (widen1 P) (super P) T U \<le> V"
      by(rule widen1_rtrancl_into_widen[OF wfP])
    with W have "P \<turnstile> W \<le> V" by simp }
  with sup itT itU itV TwV UwV show ?thesis
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
  have "closed (err (is_type P)) (lift2 (sup P))"
    by (rule closed_err_types)
  moreover
  from wf_prog have
    "(\<forall>x\<in>err (is_type P). \<forall>y\<in>err (is_type P). x \<sqsubseteq>\<^bsub>Err.le (widen P)\<^esub> x \<squnion>\<^bsub>lift2 (sup P)\<^esub> y) \<and> 
     (\<forall>x\<in>err (is_type P). \<forall>y\<in>err (is_type P). y \<sqsubseteq>\<^bsub>Err.le (widen P)\<^esub> x \<squnion>\<^bsub>lift2 (sup P)\<^esub> y)"
    by(auto simp add: lesub_def plussub_def Err.le_def lift2_def sup_widen_greater mem_def split: err.split)
  moreover from wf_prog have
    "\<forall>x\<in>err (is_type P). \<forall>y\<in>err (is_type P). \<forall>z\<in>err (is_type P). 
    x \<sqsubseteq>\<^bsub>Err.le (widen P)\<^esub> z \<and> y \<sqsubseteq>\<^bsub>Err.le (widen P)\<^esub> z \<longrightarrow> x \<squnion>\<^bsub>lift2 (sup P)\<^esub> y \<sqsubseteq>\<^bsub>Err.le (widen P)\<^esub> z"
    by (unfold lift2_def plussub_def lesub_def Err.le_def)
       (auto intro: sup_widen_smallest dest:sup_exists simp add: mem_def split: err.split)
  ultimately show ?thesis by (simp add: esl_def semilat_def sl_def Err.sl_def)
qed

subsection {* Code generator setup *}

code_pred widen1p .
lemmas [code] = widen1_def

lemma eval_widen1p_i_i_o_conv:
  "Predicate.eval (widen1p_i_i_o P T) = (\<lambda>U. P \<turnstile> T <\<^sup>1 U)"
by(auto elim: widen1p_i_i_oE intro: widen1p_i_i_oI simp add: widen1_def expand_fun_eq)

lemma rtrancl_widen1_code [code_inline]:
  "(widen1 P)^* = (\<lambda>(a, b). Predicate.holds (rtrancl_tab_FioB_i_i_i (widen1p_i_i_o P) [] a b))"
by(auto simp add: expand_fun_eq Predicate.holds_eq widen1_def Collect_def rtrancl_def mem_def rtranclp_eq_rtrancl_tab_nil eval_widen1p_i_i_o_conv intro!: rtrancl_tab_FioB_i_i_iI elim!: rtrancl_tab_FioB_i_i_iE)

end
