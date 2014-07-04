theory "Value"
  imports HOLCF
begin

subsubsection {* The semantic domain for values and environments *}

domain Value = Fn (lazy "Value \<rightarrow> Value")

fixrec Fn_project :: "Value \<rightarrow> Value \<rightarrow> Value"
 where "Fn_project\<cdot>(Fn\<cdot>f) = f"

abbreviation Fn_project_abbr (infix "\<down>Fn" 55)
  where "f \<down>Fn v \<equiv> Fn_project\<cdot>f\<cdot>v"

lemma [simp]: "\<bottom> \<down>Fn x = \<bottom>"
  by (fixrec_simp)

text {*
A chain in the domain @{typ Value} is either always bottom, or eventually @{term "Fn"} of another
chain
*}

lemma Value_chainE:
  assumes "chain Y"
  obtains "Y = (\<lambda> _ . \<bottom>)" |
          n Y' where "Y = (\<lambda> m. (if m < n then \<bottom> else Fn\<cdot>(Y' (m-n))))" "chain Y'"
proof(cases "Y = (\<lambda> _ . \<bottom>)")
  case True
  thus ?thesis by (rule that(1))
next
  case False
  hence "\<exists> i. Y i \<noteq> \<bottom>" by auto
  hence "\<exists> n. Y n \<noteq> \<bottom> \<and> (\<forall>m. Y m \<noteq> \<bottom> \<longrightarrow> m \<ge> n)"
    by (rule exE)(rule ex_has_least_nat)
  then obtain n where "Y n \<noteq> \<bottom>" and "\<forall>m. m < n \<longrightarrow> Y m = \<bottom>" by fastforce
  then obtain f where "Y n = Fn \<cdot> f" by (metis Value.exhaust)
  {
    fix i
    from `chain Y` have "Y n \<sqsubseteq> Y (i+n)" by (metis chain_mono le_add2)  
    with `Y n = _`
    have "\<exists> g. (Y (i+n) = Fn \<cdot> g)" by (metis (full_types) Value.exhaust minimal po_eq_conv)
  }
  then obtain Y' where Y': "\<And> i. Y (i + n) = Fn \<cdot> (Y' i)" by metis 

  have "Y = (\<lambda>m. if m < n then \<bottom> else Fn\<cdot>(Y' (m - n)))"
      using `\<forall>m. _` Y' by (metis add_diff_inverse add.commute)
  moreover
  have"chain Y'" using `chain Y`
    by (auto intro!:chainI elim: chainE  simp add: Value.inverts[symmetric] Y'[symmetric] simp del: Value.inverts)
  ultimately
  show ?thesis by (rule that(2))
qed

end
