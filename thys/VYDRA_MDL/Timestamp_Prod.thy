theory Timestamp_Prod
  imports Timestamp
begin

instantiation prod :: (timestamp, timestamp) timestamp
begin

definition tfin_prod :: "('a \<times> 'b) set" where
  "tfin_prod = tfin \<times> tfin"

definition \<iota>_prod :: "nat \<Rightarrow> 'a \<times> 'b" where
  "\<iota>_prod n = (\<iota> n, \<iota> n)"

fun sup_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b" where
  "sup_prod (a, b) (c, d) = (sup a c, sup b d)"

fun less_eq_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool" where
  "less_eq_prod (a, b) (c, d) \<longleftrightarrow> a \<le> c \<and> b \<le> d"

definition less_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool" where
  "less_prod x y \<longleftrightarrow> x \<le> y \<and> x \<noteq> y"

instance
  apply standard
              apply (auto simp: add.commute zero_prod_def less_prod_def)[7]
  subgoal for i j
    using \<iota>_mono \<iota>_mono less_le
    by (fastforce simp: \<iota>_prod_def less_prod_def)
  subgoal for i
    by (auto simp: \<iota>_prod_def tfin_prod_def intro: \<iota>_tfin)
  subgoal for x i
    apply (cases x)
    using \<iota>_progressing
    by (auto simp: tfin_prod_def \<iota>_prod_def)
  apply (auto simp: zero_prod_def tfin_prod_def intro: zero_tfin)[1]
  subgoal for c d
    by (cases c; cases d) (auto simp: tfin_prod_def intro: tfin_closed)
  subgoal for c d a
    by (cases c; cases d; cases a) (auto simp add: add_mono)
  subgoal for a c
    apply (cases a; cases c)
    apply (auto simp: tfin_prod_def zero_prod_def)
    apply (metis add.right_neutral add_pos less_eq_prod.simps less_prod_def order_less_le prod.inject timestamp_class.add_mono)
    done
  done

end

end
