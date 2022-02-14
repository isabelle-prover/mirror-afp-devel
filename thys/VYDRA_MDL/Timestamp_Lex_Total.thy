theory Timestamp_Lex_Total
  imports Timestamp
begin

instantiation prod :: (timestamp_total_strict, timestamp_total_strict) timestamp_total_strict
begin

definition tfin_prod :: "('a \<times> 'b) set" where
  "tfin_prod = tfin \<times> UNIV"

definition \<iota>_prod :: "nat \<Rightarrow> 'a \<times> 'b" where
  "\<iota>_prod n = (\<iota> n, \<iota> n)"

fun sup_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b" where
  "sup_prod (a, b) (c, d) = (if a < c then (c, d) else if c < a then (a, b) else (a, sup b d))"

fun less_eq_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool" where
  "less_eq_prod (a, b) (c, d) \<longleftrightarrow> a < c \<or> (a = c \<and> b \<le> d)"

definition less_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool" where
  "less_prod x y \<longleftrightarrow> x \<le> y \<and> x \<noteq> y"

instance
  apply standard
         apply (auto simp: zero_prod_def less_prod_def)[2]
  subgoal for x y z
    using order.strict_trans
    by (cases x; cases y; cases z) auto
  subgoal for x y
    by (cases x; cases y) auto
  subgoal for x y
    by (cases x; cases y) (auto simp add: sup.commute sup.strict_order_iff)
  subgoal for x y
    apply (cases x; cases y)
    apply (auto simp add: sup.commute sup.strict_order_iff)
    apply (metis sup.absorb_iff2 sup.order_iff timestamp_total)
    done
  subgoal for y x z
    by (cases x; cases y; cases z) auto
  subgoal for i j
    using \<iota>_mono less_le
    apply (auto simp: \<iota>_prod_def less_prod_def)
    by (simp add: \<iota>_mono)
  subgoal for i
    by (auto simp: \<iota>_prod_def tfin_prod_def intro: \<iota>_fin)
  subgoal for x i
    apply (cases x)
    apply (auto simp: \<iota>_prod_def tfin_prod_def)
    apply (metis \<iota>_progressing dual_order.refl order_less_le)
    done
        apply (auto simp: tfin_prod_def tfin_closed)[1]
  apply (auto simp: zero_prod_def tfin_prod_def intro: zero_tfin)[1]
  subgoal for c d
    apply (cases c; cases d)
    apply (auto simp: tfin_prod_def intro: tfin_closed)
    done
  subgoal for c d a
    by (cases c; cases d; cases a) (auto simp: add_mono add_mono_strict_total)
  subgoal for a c
    apply (cases a; cases c)
    apply (auto simp: tfin_prod_def zero_prod_def)
    apply (metis less_eq_prod.simps add.right_neutral add_mono_strict_total less_prod_def order_less_le prod.inject)
    done
  subgoal for a b
    apply (cases a; cases b)
    apply (auto)
       apply (metis antisym_conv1 timestamp_total)
      apply (metis antisym_conv1 timestamp_total)
     apply (metis antisym_conv1 timestamp_total)
    apply (metis timestamp_total)
    done
  subgoal for a c b
    apply (cases a; cases c; cases b)
    apply (auto simp: zero_prod_def tfin_prod_def)
         apply (metis less_eq_prod.simps aux less_prod_def order_less_imp_le order_less_irrefl prod.sel(1))
    using zero_tfin apply blast
       apply (metis less_eq_prod.simps add_pos less_prod_def order_less_le prod.inject)
    using zero_tfin apply blast
     apply (smt (z3) add_0 aux less_eq_prod.simps less_prod_def order_le_less order_le_less_trans order_less_irrefl)
    using less_prod_def
    apply force
    done
  subgoal for c d a
    apply (cases c; cases d; cases a)
    apply (auto simp add: add_mono_strict_total less_prod_def order.strict_implies_order)
      apply (metis add_mono_strict_total sup.strict_order_iff)
     apply (metis add_mono_strict_total sup.strict_order_iff)
    by (metis add_mono_strict_total dual_order.order_iff_strict less_le_not_le)
  done

end

end
