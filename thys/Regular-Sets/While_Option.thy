header {* A While-Combinator With Optional Result *}

(* Should become part of Library *)

theory While_Option
imports Main
begin

definition while :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a option" where
"while b c s = (if (\<exists>k. ~ b ((c ^^ k) s))
   then Some ((c ^^ (LEAST k. ~ b ((c ^^ k) s))) s)
   else None)"

theorem while_unfold[code]:
"while b c s = (if b s then while b c (c s) else Some s)"
proof cases
  assume "b s"
  show ?thesis
  proof (cases "\<exists>k. ~ b ((c ^^ k) s)")
    case True
    then obtain k where 1: "~ b ((c ^^ k) s)" ..
    with `b s` obtain l where "k = Suc l" by (cases k) auto
    with 1 have "~ b ((c ^^ l) (c s))" by (auto simp: funpow_swap1)
    then have 2: "\<exists>l. ~ b ((c ^^ l) (c s))" ..
    from 1
    have "(LEAST k. ~ b ((c ^^ k) s)) = Suc (LEAST l. ~ b ((c ^^ Suc l) s))"
      by (rule Least_Suc) (simp add: `b s`)
    also have "... = Suc (LEAST l. ~ b ((c ^^ l) (c s)))"
      by (simp add: funpow_swap1)
    finally
    show ?thesis 
      using True 2 `b s` by (simp add: funpow_swap1 while_def)
  next
    case False
    then have "~ (\<exists>l. ~ b ((c ^^ Suc l) s))" by blast
    then have "~ (\<exists>l. ~ b ((c ^^ l) (c s)))"
      by (simp add: funpow_swap1)
    with False  `b s` show ?thesis by (simp add: while_def)
  qed
next
  assume [simp]: "~ b s"
  have least: "(LEAST k. ~ b ((c ^^ k) s)) = 0"
    by (rule Least_equality) auto
  moreover 
  have "\<exists>k. ~ b ((c ^^ k) s)" by (rule exI[of _ "0::nat"]) auto
  ultimately show ?thesis unfolding while_def by auto 
qed

lemma while_stop:
assumes "while b c s = Some t"
shows "~ b t"
proof -
  from assms have ex: "\<exists>k. ~ b ((c ^^ k) s)"
  and t: "t = (c ^^ (LEAST k. ~ b ((c ^^ k) s))) s"
    by (auto simp: while_def split: if_splits)
  from LeastI_ex[OF ex]
  show "~ b t" unfolding t .
qed

theorem while_rule:
assumes step: "!!s. P s ==> b s ==> P (c s)"
and result: "while b c s = Some t"
and init: "P s"
shows "P t"
proof -
  def k == "LEAST k. ~ b ((c ^^ k) s)"
  from assms have t: "t = (c ^^ k) s"
    by (simp add: while_def k_def split: if_splits)    
  have 1: "ALL i<k. b ((c ^^ i) s)"
    by (auto simp: k_def dest: not_less_Least)

  { fix i assume "i <= k" then have "P ((c ^^ i) s)"
      by (induct i) (auto simp: init step 1) }
  thus "P t" by (auto simp: t)
qed

end
