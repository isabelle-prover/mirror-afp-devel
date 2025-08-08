section \<open> MLTL formula progresion \<close>

theory MLTL_Formula_Progression
                                
imports Mission_Time_LTL.MLTL_Properties

begin

subsection \<open>Algorithm\<close>

fun weight_operators:: "'a mltl \<Rightarrow> nat" where
"weight_operators True\<^sub>m = 1"                               
  | "weight_operators False\<^sub>m = 1"                           
  | "weight_operators (Prop\<^sub>m (p))  = 1"
  | "weight_operators (F1 And\<^sub>m F2)  = weight_operators F1 + weight_operators F2 + 1"
  | "weight_operators (F1 Or\<^sub>m F2)  =  weight_operators F1 + weight_operators F2 + 1"
  | "weight_operators (Not\<^sub>m F) = 1 + weight_operators F "
  | "weight_operators (F1 U\<^sub>m [a,b] F2)  = weight_operators F1 + weight_operators F2 + 1 + a+ b"
  | "weight_operators (F1 R\<^sub>m [a,b] F2) = 10 + weight_operators F1 + weight_operators F2 + 1+ a+ b"
  | "weight_operators (G\<^sub>m [a,b] F)  = 10 + weight_operators F+ a+ b"
  | "weight_operators (F\<^sub>m [a,b] F)  =  1 + weight_operators F+ a+ b"

function formula_progression_len1:: "'a mltl \<Rightarrow> 'a set \<Rightarrow> 'a mltl"  where 
  "formula_progression_len1 True\<^sub>m tr_entry = True\<^sub>m"                               
  | "formula_progression_len1 False\<^sub>m tr_entry = False\<^sub>m"                           
  | "formula_progression_len1 (Prop\<^sub>m (p)) tr_entry = (if p \<in> tr_entry then True\<^sub>m else False\<^sub>m)"                        
  | "formula_progression_len1 (Not\<^sub>m F) tr_entry = Not\<^sub>m (formula_progression_len1 F tr_entry)"
  | "formula_progression_len1 (F1 And\<^sub>m F2) tr_entry = (formula_progression_len1 F1 tr_entry) And\<^sub>m (formula_progression_len1 F2 tr_entry) "
  | "formula_progression_len1 (F1 Or\<^sub>m F2) tr_entry = (formula_progression_len1 F1 tr_entry) Or\<^sub>m (formula_progression_len1 F2 tr_entry) "
  | "formula_progression_len1 (F1 U\<^sub>m [a,b] F2) tr_entry =  
      (if (0<a \<and> a\<le>b) then (F1 U\<^sub>m [(a-1), (b-1)] F2)
      else (if (0=a \<and> a<b) then ((formula_progression_len1 F2 tr_entry) Or\<^sub>m ((formula_progression_len1 F1 tr_entry) And\<^sub>m (F1 U\<^sub>m [0, (b-1)] F2)))
      else (formula_progression_len1 F2 tr_entry)))"
  | "formula_progression_len1 (F1 R\<^sub>m [a,b] F2) tr_entry = Not\<^sub>m (formula_progression_len1 ((Not\<^sub>m F1) U\<^sub>m [a,b] (Not\<^sub>m F2)) tr_entry)"
  | "formula_progression_len1 (G\<^sub>m [a,b] F) tr_entry = Not\<^sub>m (formula_progression_len1 (F\<^sub>m [a,b] (Not\<^sub>m F)) tr_entry)"
  | "formula_progression_len1 (F\<^sub>m [a,b] F) tr_entry =  
    (if 0< a \<and> a\<le> b then  (F\<^sub>m [(a-1), (b-1)] F) 
    else if (0 = a \<and> a < b) then ((formula_progression_len1 F tr_entry) Or\<^sub>m (F\<^sub>m [0, (b-1)] F))
    else (formula_progression_len1 F tr_entry))"
  apply auto 
  by (meson mltl.exhaust)
termination apply (relation  "measure (\<lambda>(F,tr_entry). (weight_operators F))")
  by auto

text \<open> Note that formula progression needs to be defined when the
  length of the trace is 0. In this case, we define it to just
  return the original formula. \<close>
fun formula_progression:: "'a mltl \<Rightarrow> 'a set list \<Rightarrow> 'a mltl" 
  where "formula_progression F tr = 
    (if length tr = 0 then F 
    else (if length tr = 1 then (formula_progression_len1 F (tr!0)) 
    else (formula_progression (formula_progression_len1 F (tr ! 0)) (drop 1 tr))))"

value "take 2 ([0::nat, 1, 2, 3]::nat list)"
value "drop 2 ([0::nat, 1, 2, 3]::nat list)"

(*We thank Dmitriy Traytel for suggesting this
lemma and pointing out how it can simplify our proofs*)
lemma formula_progression_alt: 
"formula_progression F xs = fold (\<lambda>x F. formula_progression_len1 F x) xs F"
  apply (induct xs arbitrary: F) 
   apply (subst formula_progression.simps; simp_all)
  by (smt (verit, best) Cons_nth_drop_Suc One_nat_def diff_Suc_Suc drop0 fold_simps(2) formula_progression.elims length_0_conv length_drop length_greater_0_conv list.discI list.simps(1) zero_diff)
 

subsection \<open>Proofs\<close>

subsubsection \<open>Empty Trace Semantics of MLTL\<close>

lemma semantics_global:
  shows "[] \<Turnstile>\<^sub>m (G\<^sub>m [0,1] \<phi>)"
  using semantics_mltl.simps(8)
  by blast

lemma semantics_future:
  shows "[] \<Turnstile>\<^sub>m (Not\<^sub>m (F\<^sub>m [0,1] (Not\<^sub>m \<phi>)))"
  using semantics_mltl.simps(7)
  semantics_mltl.simps(4) by simp

subsubsection \<open>Well-definedness Properties\<close>

lemma formula_progression_well_definedness_preserved_len1:
  assumes "intervals_welldef \<phi>"
  shows "intervals_welldef (formula_progression_len1 \<phi> \<pi>)"
  using assms apply (induct \<phi>) using diff_le_mono by simp_all

lemma formula_progression_well_definedness_preserved:
  assumes "intervals_welldef \<phi>"
  shows "intervals_welldef (formula_progression \<phi> \<pi>)"
  using assms apply (induct \<pi> arbitrary: \<phi>) apply simp 
  unfolding formula_progression_alt
  by (simp add: formula_progression_well_definedness_preserved_len1) 
 
subsubsection \<open>Theorem 1\<close>

text \<open> Helper lemma for Theorem 1 \<close>
lemma formula_progression_identity:
  fixes \<phi>::"'a mltl"
  fixes k::"nat"
  assumes "k < length \<pi>"
  shows "formula_progression (formula_progression \<phi> (take k \<pi>)) [\<pi> ! k] 
  = formula_progression \<phi> (take (k+1) \<pi>)"
  using assms
proof (induct k arbitrary: \<pi> \<phi>)
  case 0
  then have len_take1: "length (take 1 \<pi>) = 1"
    by (simp add: Suc_leI)
 then have same_fp: "formula_progression \<phi> [\<pi> ! 0] =  formula_progression \<phi> (take 1 \<pi>)"
   by auto
  have "take 0 \<pi> = []"
    by auto
  then have "formula_progression \<phi> (take 0 \<pi>) = \<phi>"
    by auto
  then show ?case 
    using same_fp by auto
next
  case (Suc k)
  {assume *: "Suc k = 1"
    then have len_pi: "length \<pi> \<ge> 2"
      using Suc(2) by auto
    then have take2: "take 2 \<pi> = [\<pi> ! 0, \<pi> ! 1]"
      by (smt (verit) "*" Cons_nth_drop_Suc One_nat_def Suc.prems Suc_1 dual_order.strict_trans id_take_nth_drop less_numeral_extra(1) self_append_conv2 take0 take_Suc_Cons)
    have take1: "take 1 \<pi> = [\<pi> ! 0]"
      using len_pi 
      by (metis "*" Cons_eq_append_conv One_nat_def Suc.prems dual_order.strict_trans less_numeral_extra(1) take0 take_Suc_conv_app_nth)
    have "formula_progression (formula_progression \<phi> [\<pi> ! 0])
     [\<pi> ! 1] =
    formula_progression \<phi> [\<pi> ! 0, \<pi> ! 1]"
      by fastforce
    then have ?case
      using * take1 take2 
      using Suc_1 plus_1_eq_Suc by presburger
  } moreover {assume *: "Suc k > 1"
   have "formula_progression \<phi> (take (Suc k + 1) \<pi>) = 
formula_progression (formula_progression \<phi> [\<pi> ! 0]) (drop 1 (take (Suc k + 1) \<pi>))"
     using Suc by simp
  let ?\<psi> = "formula_progression \<phi> [\<pi> ! 0]"
  let ?\<xi> = "drop 1 \<pi>"
  have "drop 1 (take (Suc k + 1) \<pi>) = take (k+1) ?\<xi>"
    by (simp add: drop_take)
  have ih_prem: "k < length (take (k+1) ?\<xi>)"
    using Suc(2) by simp
  have "take k (take (k + 1) (drop 1 \<pi>)) = take k (drop 1 \<pi>)"
    by simp
  then have "formula_progression (formula_progression \<phi> [\<pi> ! 0])
       (take k (take (k + 1) (drop 1 \<pi>))) = formula_progression \<phi> (take (k+1) \<pi>)"
    using Suc(2) * 
    by (smt (verit) Nat.add_diff_assoc Nat.diff_diff_right add_diff_cancel_left' diff_add_zero drop_take dual_order.strict_trans formula_progression.elims leI le_numeral_extra(4) length_Cons length_take less_2_cases_iff list.size(3) min.absorb4 not_less_iff_gr_or_eq nth_Cons_0 nth_take plus_1_eq_Suc zero_less_one zero_neq_one)
  then have ?case
    using Suc(1)[OF ih_prem, of ?\<psi>]
    by (smt (verit) "*" One_nat_def Suc.hyps Suc.prems Suc_eq_plus1 \<open>drop 1 (take (Suc k + 1) \<pi>) = take (k + 1) (drop 1 \<pi>)\<close> \<open>formula_progression \<phi> (take (Suc k + 1) \<pi>) = formula_progression (formula_progression \<phi> [\<pi> ! 0]) (drop 1 (take (Suc k + 1) \<pi>))\<close> \<open>take k (take (k + 1) (drop 1 \<pi>)) = take k (drop 1 \<pi>)\<close> drop_all dual_order.strict_trans length_drop length_greater_0_conv less_diff_conv nle_le nth_drop plus_1_eq_Suc) 
  }
  ultimately show ?case using Suc(2)
    by auto
qed

text \<open> Theorem 1 \<close>
theorem formula_progression_decomposition:
  fixes \<phi>::"'a mltl"
  assumes "k \<ge> 1"
  assumes "k \<le> length \<pi>"
  shows "formula_progression (formula_progression \<phi> (take k \<pi>)) (drop k \<pi>)
    = formula_progression \<phi> \<pi>"
  using assms
proof (induct k)
  case 0
  then show ?case by simp
next
  case (Suc k)
  {assume *: "Suc k = 1"
    (* Assuming that Suc k = 1 and the length of the trace is 1 *)
    {assume **: "length \<pi> = 1"
      have h1: "formula_progression \<phi> \<pi> =
     formula_progression_len1 \<phi> (\<pi> ! 0)"
        using * **
        by (metis formula_progression.simps zero_neq_one) 
      have h2a:"formula_progression (formula_progression \<phi> (take (Suc k) \<pi>))
     (drop (Suc k) \<pi>) = formula_progression \<phi> (take (Suc k) \<pi>)"
        using * ** 
        by simp
      have h2b: "formula_progression \<phi> (take (Suc k) \<pi>) = formula_progression_len1 \<phi> (\<pi>!0)"
        using * **
        using h1 by auto 
      have ?case using h1 h2a h2b
        by argo
    } moreover {assume ** : "length \<pi> > 1" (* Assuming that Suc k = 1 and the length of the trace is > 1 *)
      then have h1: "formula_progression \<phi> \<pi> = formula_progression (formula_progression_len1 \<phi> (\<pi> ! 0))
                (drop 1 \<pi>)"
        using formula_progression.simps[of \<phi> \<pi>]
        by auto
      then have h2: "formula_progression (formula_progression \<phi> (take (Suc k) \<pi>))
     (drop (Suc k) \<pi>) = formula_progression (formula_progression \<phi> ([\<pi>!0]))
     (drop 1 \<pi>)"
        using *
        by (metis "**" One_nat_def Suc_lessD append_Nil take_0 take_Suc_conv_app_nth) 
      have "(formula_progression \<phi> [\<pi> ! 0]) = formula_progression_len1 \<phi> (\<pi> ! 0)"
        using formula_progression.simps by simp
      then have ?case
        using * h1 h2 by simp
    }
    ultimately have ?case
      using Suc.prems(2) by linarith
  } moreover {assume *: "Suc k > 1"
    then have simplify1: "formula_progression (formula_progression \<phi> (take k \<pi>)) (drop k \<pi>) 
            = formula_progression
                (formula_progression_len1
                  (formula_progression \<phi> (take k \<pi>)) (drop k \<pi> ! 0))
                (drop 1 (drop k \<pi>))"
      using formula_progression.simps[of "formula_progression \<phi> (take k \<pi>)" "(drop k \<pi>)"]
      Suc(3)
      by (metis cancel_comm_monoid_add_class.diff_cancel diff_is_0_eq formula_progression.elims length_drop not_less_eq_eq)
    have simplify2: "drop k \<pi> ! 0= \<pi>!k \<and> drop 1 (drop k \<pi>) = drop (k+1) \<pi>"
      using *  Suc(3) 
      by (metis Cons_nth_drop_Suc Suc_eq_plus1 Suc_le_lessD drop_drop nth_Cons_0 plus_1_eq_Suc)
     then have simplify3: "formula_progression (formula_progression \<phi> (take k \<pi>)) (drop k \<pi>) 
        =  formula_progression
                (formula_progression_len1
                  (formula_progression \<phi> (take k \<pi>)) (\<pi>!k))
                (drop (k+1) \<pi>)"
       using simplify1 by presburger
     have "(formula_progression (formula_progression \<phi> (take k \<pi>)) ([\<pi> ! k])) = 
          formula_progression_len1 (formula_progression \<phi> (take k \<pi>)) (\<pi>!k)"
       by simp
    then have equality1: "formula_progression (formula_progression \<phi> (take k \<pi>)) (drop k \<pi>)
      = formula_progression (formula_progression (formula_progression \<phi> (take k \<pi>)) ([\<pi> ! k])) (drop (k+1) \<pi>)"
      using simplify3 by presburger
    have equality2: "formula_progression (formula_progression \<phi> (take k \<pi>)) ([\<pi> ! k]) = formula_progression \<phi> (take (k+1) \<pi>)"
      using * Suc(3) formula_progression_identity Suc_le_lessD
      by blast
      then have ?case
        by (metis "*" Suc.hyps Suc.prems(2) Suc_eq_plus1 Suc_leD \<open>formula_progression (formula_progression \<phi> (take k \<pi>)) [\<pi> ! k] = formula_progression_len1 (formula_progression \<phi> (take k \<pi>)) (\<pi> ! k)\<close> less_Suc_eq_le simplify3) 
  }
  ultimately show ?case 
    by linarith
qed

subsubsection \<open>Theorem 2\<close>

text \<open> Base case for Theorem 2 \<close>
lemma satisfiability_preservation_len1:
  fixes \<phi>::"'a mltl"
  assumes "1 < length \<pi>"
  assumes "intervals_welldef \<phi>"
  shows "semantics_mltl (drop 1 \<pi>) (formula_progression_len1 \<phi> (\<pi> ! 0))
    \<longleftrightarrow> semantics_mltl \<pi> \<phi>"
 using assms 
    proof (induction \<phi>)
      case True_mltl
      then show ?case by auto
    next
      case False_mltl
      then show ?case by auto
    next
      case (Prop_mltl p)
      then show ?case using formula_progression_len1.simps(3)[of p "\<pi> ! 0"]
        using Prop_mltl by force
    next
      case (Not_mltl F)
      then show ?case by simp
    next
      case (And_mltl F1 F2)
      then show ?case by simp
    next
      case (Or_mltl F1 F2)
      then show ?case by simp
    next
      case (Future_mltl a b F)
      {assume * :"0 < a \<and> a \<le> b"
        have equiv: "((a - 1 \<le> i \<and> i \<le> b - 1) \<and> semantics_mltl (drop i (drop 1 \<pi>)) F) \<longleftrightarrow>
        ((a \<le> (i+1) \<and> (i+1) \<le> b) \<and> semantics_mltl (drop (i+1) \<pi>) F)"
          for i 
          using "*" Nat.le_diff_conv2 le_diff_conv by auto
        have d1: "(\<exists>i. (a - 1 \<le> i \<and> i \<le> b - 1) \<and>
         semantics_mltl (drop i (drop 1 \<pi>)) F) \<longrightarrow>
    (\<exists>i. (a \<le> i \<and> i \<le> b) \<and> semantics_mltl (drop i \<pi>) F)"
          using equiv by auto
        have d2: "(\<exists>i. (a \<le> i \<and> i \<le> b) \<and> semantics_mltl (drop i \<pi>) F) \<longrightarrow>
      (\<exists>i. (a - 1 \<le> i \<and> i \<le> b - 1) \<and>
         semantics_mltl (drop i (drop 1 \<pi>)) F)"
          using equiv 
          by (metis "*" Suc_diff_Suc Suc_eq_plus1 diff_zero linorder_not_less not_gr_zero)
        then have "(\<exists>i. (a - 1 \<le> i \<and> i \<le> b - 1) \<and>
          semantics_mltl (drop i (drop 1 \<pi>)) F) \<longleftrightarrow>
        (\<exists>i. (a \<le> i \<and> i \<le> b) \<and> semantics_mltl (drop i \<pi>) F)"
          using d1 d2 by auto
        then have "semantics_mltl (drop 1 \<pi>) (Future_mltl (a - 1) (b - 1) F) =
            semantics_mltl \<pi> (Future_mltl a b F)"
           using semantics_mltl.simps(7)[of "(drop 1 \<pi>)" "a - 1" "b - 1" F]
           semantics_mltl.simps(7)[of "\<pi>" "a" "b" F] *
           using dual_order.trans by auto
      then have ?case
        using formula_progression_len1.simps(10)[of a b F "\<pi> ! 0"]
        using  "*"
        by presburger
    }
    moreover {assume *: "0 = a \<and> a < b"
      have fp_is: "formula_progression_len1 (Future_mltl a b F) (\<pi> ! 0) =
             Or_mltl (formula_progression_len1 F (\<pi> ! 0)) (Future_mltl 0 (b - 1) F)"
        using * by auto
      have length_gt:"length \<pi> > 0"
        using Future_mltl by auto
      have rhs: "semantics_mltl \<pi> (Future_mltl a b F) = (a < length \<pi> \<and> (\<exists>i. (a \<le> i \<and> i \<le> b) \<and> semantics_mltl (drop i \<pi>) F))"
        using semantics_mltl.simps(7)[of \<pi> a b F] * by auto
      have "semantics_mltl (drop 1 \<pi>) (Or_mltl (formula_progression_len1 F (\<pi> ! 0)) (Future_mltl 0 (b - 1) F))
      =  (semantics_mltl (drop 1 \<pi>) (formula_progression_len1 F (\<pi> ! 0))) \<or> (semantics_mltl (drop 1 \<pi>) (Future_mltl 0 (b - 1) F))"
        by auto
      then have lhs:"semantics_mltl (drop 1 \<pi>) (formula_progression_len1 (Future_mltl a b F) (\<pi> ! 0)) =
    (semantics_mltl (drop 1 \<pi>) (formula_progression_len1 F (\<pi> ! 0))) \<or> (semantics_mltl (drop 1 \<pi>) (Future_mltl 0 (b - 1) F))"
        using fp_is 
        by simp
      have b_prop: "b-1 \<ge> 0" using * by auto
      have  "((\<exists>i. (0 \<le> i \<and> i \<le> b) \<and> semantics_mltl (drop i \<pi>) F)) = 
    (semantics_mltl \<pi> F \<or> 
     (0 < length (drop 1 \<pi>) \<and> (\<exists>i. (0 \<le> i \<and> i \<le> b - 1) \<and> semantics_mltl (drop (i+1) \<pi>) F)))"
      proof - 
        {assume **: "length \<pi> = 1"
          then have ?thesis  using * Future_mltl by auto
        } moreover {assume **: "length \<pi> > 1"
          have h1: "(\<exists>i. (0 \<le> i \<and> i \<le> b) \<and> semantics_mltl (drop i \<pi>) F) \<longrightarrow>
          (semantics_mltl \<pi> F \<or> (\<exists>i. (0 \<le> i \<and> i \<le> b - 1) \<and> semantics_mltl (drop (i + 1) \<pi>) F))"
            by (metis Suc_eq_plus1 Suc_pred' bot_nat_0.extremum diff_le_mono drop_0 le_imp_less_Suc less_one linorder_le_less_linear)
          have h2: "(semantics_mltl \<pi> F \<or> (\<exists>i. (0 \<le> i \<and> i \<le> b - 1) \<and> semantics_mltl (drop (i + 1) \<pi>) F)) \<longrightarrow> 
          (\<exists>i. (0 \<le> i \<and> i \<le> b) \<and> semantics_mltl (drop i \<pi>) F)"

            by (metis "*" Nat.le_diff_conv2 drop0 gr_implies_not0 less_one linorder_le_less_linear zero_le)
          have "(\<exists>i. (0 \<le> i \<and> i \<le> b) \<and> semantics_mltl (drop i \<pi>) F) =
          (semantics_mltl \<pi> F \<or> (\<exists>i. (0 \<le> i \<and> i \<le> b - 1) \<and> semantics_mltl (drop (i + 1) \<pi>) F))"
            using h1 h2 by auto
          then have ?thesis 
            using **
            by simp 
        }
        ultimately show ?thesis using Future_mltl(2) 
          by fastforce
      qed
      then have  "(a < length \<pi> \<and> (\<exists>i. (a \<le> i \<and> i \<le> b) \<and> semantics_mltl (drop i \<pi>) F)) =
    (semantics_mltl \<pi> F \<or>  (0 \<le> b - 1 \<and>
     0 < length (drop 1 \<pi>) \<and> (\<exists>i. (0 \<le> i \<and> i \<le> b - 1) \<and> semantics_mltl (drop i (drop 1 \<pi>)) F)))"
        using length_gt * by auto
      then have  "(a < length \<pi> \<and> (\<exists>i. (a \<le> i \<and> i \<le> b) \<and> semantics_mltl (drop i \<pi>) F)) = 
    (semantics_mltl \<pi> F \<or> (semantics_mltl (drop 1 \<pi>) (Future_mltl 0 (b - 1) F)))"
        using semantics_mltl.simps(7)[of "(drop 1 \<pi>)" 0 "b-1" F] 
        by simp
      then have  "(a < length \<pi> \<and> (\<exists>i. (a \<le> i \<and> i \<le> b) \<and> semantics_mltl (drop i \<pi>) F)) = 
        (semantics_mltl (drop 1 \<pi>) (formula_progression_len1 F (\<pi> ! 0))) \<or> (semantics_mltl (drop 1 \<pi>) (Future_mltl 0 (b - 1) F))"
        using Future_mltl 
        by (metis intervals_welldef.simps(7))
      then have ?case
        using lhs rhs fp_is * Future_mltl 
        by fastforce
    } moreover {assume * :"\<not>(0 = a \<and> a < b) \<and> \<not> (0 < a \<and> a \<le> b)"
      then have a_eq_b: "a = 0 \<and> b = 0"
        using Future_mltl(3) using intervals_welldef.simps(7)[of a b F]
        by auto
      then have "formula_progression_len1 (Future_mltl a b F) (\<pi> ! 0) = formula_progression_len1 F (\<pi> ! 0)"
        by auto
      then have h1: "semantics_mltl (drop 1 \<pi>) (formula_progression_len1 (Future_mltl a b F) (\<pi> ! 0)) =  semantics_mltl \<pi> F"  
       using Future_mltl
       by simp 
     have "semantics_mltl \<pi> F =  semantics_mltl \<pi> (Future_mltl 0 0 F)"
       using  semantics_mltl.simps(7)[of "\<pi>" 0 0 F] *
       Future_mltl(2)
       by force
     then have ?case
       using  h1 a_eq_b by blast
    }
    ultimately show ?case
      by blast
    next
      case (Global_mltl a b F)
      have " semantics_mltl (drop 1 \<pi>) (formula_progression_len1 (Global_mltl a b F) (\<pi> ! 0)) =
     (\<not> (semantics_mltl (drop 1 \<pi>) (formula_progression_len1 (Future_mltl a b (Not_mltl F)) (\<pi> ! 0))))"
        unfolding formula_progression_len1.simps by auto
      have "((formula_progression_len1 (Future_mltl a b (Not_mltl F)) (\<pi> ! 0))) =
              (if 0 < a \<and> a \<le> b then Future_mltl (a - 1) (b - 1) (Not_mltl F)
        else if 0 = a \<and> a < b
        then Or_mltl (formula_progression_len1 (Not_mltl F) (\<pi> ! 0))
              (Future_mltl 0 (b - 1) (Not_mltl F))
        else formula_progression_len1 (Not_mltl F) (\<pi> ! 0))"
        using formula_progression_len1.simps(10)
        by simp
      {assume *: "0 < a \<and> a \<le> b"
        have d1: "(\<forall>i. ((a - 1 \<le> i \<and> i \<le> b - 1) \<longrightarrow> semantics_mltl (drop (i+1) \<pi>) F)) \<Longrightarrow> (\<And>i. a \<le> i \<and> i \<le> b \<Longrightarrow> semantics_mltl (drop i \<pi>) F)"
        proof - 
          fix i
          assume all_prop: "(\<forall>i. ((a - 1 \<le> i \<and> i \<le> b - 1) \<longrightarrow> semantics_mltl (drop (i+1) \<pi>) F))"
          assume " a \<le> i \<and> i \<le> b"
          then have "a-1 \<le> i-1 \<and> i - 1 \<le> b - 1"
            by auto
          then have "semantics_mltl (drop ((i-1)+1) \<pi>) F"
            using all_prop by simp
          then show " semantics_mltl (drop i \<pi>) F"
            using assms * 
            by (metis One_nat_def Suc_leI \<open>a \<le> i \<and> i \<le> b\<close> le_add_diff_inverse2 order_less_le_trans)
        qed
        have d2: "(\<forall>i. a \<le> i \<and> i \<le> b \<longrightarrow> semantics_mltl (drop i \<pi>) F) \<Longrightarrow> (\<And>i. ((a - 1 \<le> i \<and> i \<le> b - 1) \<Longrightarrow> semantics_mltl (drop (i+1) \<pi>) F))"
        proof - 
          fix i
          assume all_prop: "(\<forall>i. a \<le> i \<and> i \<le> b \<longrightarrow> semantics_mltl (drop i \<pi>) F)"
          assume " a-1 \<le> i \<and> i \<le> b-1"
          then have "a \<le> i+1 \<and> i+1 \<le> b"
            using * by auto
          then show "semantics_mltl (drop (i+1) \<pi>) F"
            using assms * all_prop by blast
        qed
        have all_conn: "(\<forall>i. (a - 1 \<le> i \<and> i \<le> b - 1) \<longrightarrow> semantics_mltl (drop (i+1) \<pi>) F) = (\<forall>i. a \<le> i \<and> i \<le> b \<longrightarrow> semantics_mltl (drop i \<pi>) F)"
          using d1 d2 by blast
         have "(\<not> semantics_mltl (drop 1 \<pi>) ( Future_mltl (a - 1) (b - 1) (Not_mltl F))) =  (\<not> (a - 1 < length (drop 1 \<pi>) \<and>
          (\<exists>i. (a - 1 \<le> i \<and> i \<le> b - 1) \<and> \<not> semantics_mltl (drop i (drop 1 \<pi>)) F)))"
          using * unfolding semantics_mltl.simps by auto
        then have "(\<not> semantics_mltl (drop 1 \<pi>) ( Future_mltl (a - 1) (b - 1) (Not_mltl F))) =  ((a - 1 \<ge> length (drop 1 \<pi>) \<or>
          \<not>(\<exists>i. (a - 1 \<le> i \<and> i \<le> b - 1) \<and> \<not> semantics_mltl (drop i (drop 1 \<pi>)) F)))"
          by auto
        then have "(\<not> semantics_mltl (drop 1 \<pi>) ( Future_mltl (a - 1) (b - 1) (Not_mltl F))) =  (a \<ge> length \<pi> \<or>
          (\<forall>i. ((a - 1 \<le> i \<and> i \<le> b - 1) \<longrightarrow> semantics_mltl (drop i (drop 1 \<pi>)) F)))"
          by (metis "*" One_nat_def Suc_le_mono Suc_pred assms(1) length_0_conv length_drop length_greater_0_conv not_one_less_zero)
        then have "(\<not> semantics_mltl (drop 1 \<pi>) ( Future_mltl (a - 1) (b - 1) (Not_mltl F))) = 
        (length \<pi> \<le> a \<or> (\<forall>i. (a \<le> i \<and> i \<le> b \<longrightarrow> semantics_mltl (drop i \<pi>) F)))"
          using all_conn by simp
        then have ?case unfolding formula_progression_len1.simps semantics_mltl.simps
          using * by auto
      } moreover {assume *: " 0 = a \<and> a < b"
        have d1: "(\<forall>i. (0 \<le> i \<and> i \<le> b - 1) \<longrightarrow> semantics_mltl (drop (i+1) \<pi>) F) \<Longrightarrow> (\<And>i. 1 \<le> i \<and> i \<le> b \<Longrightarrow> semantics_mltl (drop i \<pi>) F)"
        proof - 
          assume all_prop: "(\<forall>i. (0 \<le> i \<and> i \<le> b - 1) \<longrightarrow> semantics_mltl (drop (i+1) \<pi>) F)"
          fix i 
          assume "1 \<le> i \<and> i \<le> b"
          then have "(0 \<le> i-1 \<and> i-1 \<le> b - 1)"
            by auto
          then show "semantics_mltl (drop i \<pi>) F"
            using all_prop 
            by (metis \<open>1 \<le> i \<and> i \<le> b\<close> le_add_diff_inverse2)
        qed
        have d2: "(\<forall>i. 1 \<le> i \<and> i \<le> b \<longrightarrow> semantics_mltl (drop i \<pi>) F) \<Longrightarrow> (\<And>i. (0 \<le> i \<and> i \<le> b - 1) \<Longrightarrow> semantics_mltl (drop (i+1) \<pi>) F)"
        proof - 
          assume all_prop: "(\<forall>i. 1 \<le> i \<and> i \<le> b \<longrightarrow> semantics_mltl (drop i \<pi>) F)"
          fix i
          assume "(0 \<le> i \<and> i \<le> b - 1)"
          then have "1 \<le> i+1 \<and> i+1 \<le> b"
            using * by auto
          then show "semantics_mltl (drop (i+1) \<pi>) F"
            using all_prop by blast
        qed
        have "\<not>(\<exists>i. (0 \<le> i \<and> i \<le> b - 1) \<and> \<not> semantics_mltl (drop (i+1) \<pi>) F)
          = (\<forall>i. (0 \<le> i \<and> i \<le> b - 1) \<longrightarrow> semantics_mltl (drop (i+1) \<pi>) F)"
          by blast
        then have exist_rel: "\<not>(\<exists>i. (0 \<le> i \<and> i \<le> b - 1) \<and> \<not> semantics_mltl (drop (i+1) \<pi>) F)
          = (\<forall>i. 1 \<le> i \<and> i \<le> b \<longrightarrow> semantics_mltl (drop i \<pi>) F)"
          using d1 d2 by metis
        have eq_2: "semantics_mltl \<pi> F = semantics_mltl (drop 0 \<pi>) F"
          by auto
        then have  "(semantics_mltl \<pi> F \<and>
         \<not>(\<exists>i. (0 \<le> i \<and> i \<le> b - 1) \<and> \<not> semantics_mltl (drop (i+1) \<pi>) F)) =
          (\<forall>i. 0 \<le> i \<and> i \<le> b \<longrightarrow> semantics_mltl (drop i \<pi>) F)"
          using exist_rel eq_2 
          by (metis One_nat_def Suc_leI bot_nat_0.extremum le_eq_less_or_eq)
        then have " (semantics_mltl (drop 1 \<pi>) (formula_progression_len1 F (\<pi> ! 0)) \<and>
         \<not>(\<exists>i. (0 \<le> i \<and> i \<le> b - 1) \<and> \<not> semantics_mltl (drop i (drop 1 \<pi>)) F)) =
          (\<forall>i. 0 \<le> i \<and> i \<le> b \<longrightarrow> semantics_mltl (drop i \<pi>) F)"
          using Global_mltl by auto
        then  have " (\<not> (\<not> semantics_mltl (drop 1 \<pi>) (formula_progression_len1 F (\<pi> ! 0)) \<or>
         (\<exists>i. (0 \<le> i \<and> i \<le> b - 1) \<and> \<not> semantics_mltl (drop i (drop 1 \<pi>)) F))) =
          (\<forall>i. a \<le> i \<and> i \<le> b \<longrightarrow> semantics_mltl (drop i \<pi>) F)"
          using *
          by auto
        then have "(\<not> semantics_mltl (drop 1 \<pi>)
         (Or_mltl (Not_mltl (formula_progression_len1 F (\<pi> ! 0)))
                     (Future_mltl 0 (b - 1) (Not_mltl F)))) =
    (length \<pi> \<le> a \<or> (\<forall>i. a \<le> i \<and> i \<le> b \<longrightarrow> semantics_mltl (drop i \<pi>) F))"
          using * Global_mltl unfolding semantics_mltl.simps by auto
        then have ?case using * unfolding formula_progression_len1.simps semantics_mltl.simps
          by auto
      } moreover {assume *: "\<not>(0 < a \<and> a \<le> b) \<and> \<not>(0 = a \<and> a < b)"
        have "a \<le> b"
          using Global_mltl(3) unfolding intervals_welldef.simps
          by auto
        then have **: "0 = a \<and> 0 = b"
          using * by auto
        have ind_h: "semantics_mltl (drop 1 \<pi>) (formula_progression_len1 F (\<pi> ! 0)) = semantics_mltl \<pi> F"
          using Global_mltl by auto
        have "semantics_mltl \<pi> F =
          (length \<pi> \<le> 0 \<or> (\<forall>i. 0 \<le> i \<and> i \<le> 0 \<longrightarrow> semantics_mltl (drop i \<pi>) F))"
          using Global_mltl by auto
        then have "(\<not> semantics_mltl (drop 1 \<pi>)
         (Not_mltl (formula_progression_len1 F (\<pi> ! 0)))) =
    (a \<le> b \<and> (length \<pi> \<le> a \<or> (\<forall>i. a \<le> i \<and> i \<le> b \<longrightarrow> semantics_mltl (drop i \<pi>) F)))"
          using ind_h ** unfolding semantics_mltl.simps by blast
        then have ?case using * unfolding formula_progression_len1.simps semantics_mltl.simps
          by force
      }
      ultimately show ?case by blast
    next
      case (Until_mltl F1 a b F2)
      {assume *: "0 < a \<and> a \<le> b"
        have d1: "(\<exists>i. (a \<le> i \<and> i \<le> b) \<and> semantics_mltl (drop i \<pi>) F2 \<and> (\<forall>j. a \<le> j \<and> j < i \<longrightarrow> semantics_mltl (drop j \<pi>) F1))"
          if i_ex: "(\<exists>i. (a - 1 \<le> i \<and> i \<le> b - 1) \<and> semantics_mltl (drop (i + 1) \<pi>) F2 \<and>
         (\<forall>j. a - 1 \<le> j \<and> j < i \<longrightarrow> semantics_mltl (drop (j + 1) \<pi>) F1))"
        proof -
          obtain i where i_sat: "(a - 1 \<le> i \<and> i \<le> b - 1)"
         "semantics_mltl (drop (i + 1) \<pi>) F2"
         "(\<And>j. a - 1 \<le> j \<and> j < i \<Longrightarrow> semantics_mltl (drop (j + 1) \<pi>) F1)"
            using i_ex by auto
          have h1: "a \<le> i + 1 \<and> i + 1 \<le> b"
            using *  i_sat by auto
          have h2: "semantics_mltl (drop (i+1) \<pi>) F2"
            using i_sat by blast
          have h3: "semantics_mltl (drop j \<pi>) F1" if j: "a \<le> j \<and> j < (i+1)" for j
            using i_sat(3)[of "j-1"] j  
            by (metis (no_types, lifting) "*" One_nat_def Suc_eq_plus1 Suc_leI le_add_diff_inverse2 le_imp_less_Suc linorder_not_less order_less_le_trans)
          then show ?thesis using h1 h2 h3 by auto
        qed
        have d2: "(\<exists>i. (a - 1 \<le> i \<and> i \<le> b - 1) \<and> semantics_mltl (drop (i + 1) \<pi>) F2 \<and>
         (\<forall>j. a - 1 \<le> j \<and> j < i \<longrightarrow> semantics_mltl (drop (j + 1) \<pi>) F1))" 
         if i_ex: "(\<exists>i. (a \<le> i \<and> i \<le> b) \<and>
         semantics_mltl (drop i \<pi>) F2 \<and> (\<forall>j. a \<le> j \<and> j < i \<longrightarrow> semantics_mltl (drop j \<pi>) F1))"
        proof -
          obtain i where i_sat: "(a \<le> i \<and> i \<le> b)"
         "semantics_mltl (drop i \<pi>) F2"
         "(\<And>j. a \<le> j \<and> j < i \<Longrightarrow> semantics_mltl (drop j \<pi>) F1)"
            using i_ex by auto
          then have h1: "a - 1 \<le> i-1 \<and> i-1 \<le> b - 1"
            using * i_sat(1) by auto
          have h2: "semantics_mltl (drop ((i-1)+1) \<pi>) F2"
            using i_sat * 
            by simp
          have h3: "semantics_mltl (drop (j+1) \<pi>) F1" if j: "a-1 \<le> j \<and> j < i-1" for j
            using i_sat(3)[of "j"] j  
            using i_sat(3) le_diff_conv less_diff_conv by blast
          then show ?thesis using h1 h2 h3 
            by auto
        qed
        have "(\<exists>i. (a - 1 \<le> i \<and> i \<le> b - 1) \<and> semantics_mltl (drop (i+1) \<pi>) F2 \<and>
          (\<forall>j. a - 1 \<le> j \<and> j < i \<longrightarrow> semantics_mltl (drop (j+1) \<pi>) F1)) = 
          (\<exists>i. (a \<le> i \<and> i \<le> b) \<and>
          semantics_mltl (drop i \<pi>) F2 \<and> (\<forall>j. a \<le> j \<and> j < i \<longrightarrow> semantics_mltl (drop j \<pi>) F1))"
          using d1 d2 by blast
        then have "(a - 1 < length (drop 1 \<pi>) \<and>
          (\<exists>i. (a - 1 \<le> i \<and> i \<le> b - 1) \<and> semantics_mltl (drop i (drop 1 \<pi>)) F2 \<and>
          (\<forall>j. a - 1 \<le> j \<and> j < i \<longrightarrow> semantics_mltl (drop j (drop 1 \<pi>)) F1))) =
    (a < length \<pi> \<and>
     (\<exists>i. (a \<le> i \<and> i \<le> b) \<and>
          semantics_mltl (drop i \<pi>) F2 \<and> (\<forall>j. a \<le> j \<and> j < i \<longrightarrow> semantics_mltl (drop j \<pi>) F1)))"
           using Until_mltl(3) by auto
        then have "semantics_mltl (drop 1 \<pi>) (Until_mltl F1 (a - 1) (b - 1) F2) =
          semantics_mltl \<pi> (Until_mltl F1 a b F2)"
          using * unfolding semantics_mltl.simps 
          by (meson order_trans)
        then have ?case unfolding formula_progression_len1.simps
          using * by simp
      } 
      moreover {assume *: "0 = a \<and> a < b"
        have d1: "(\<exists>i. (0 \<le> i \<and> i \<le> b) \<and>
          semantics_mltl (drop i \<pi>) F2 \<and> (\<forall>j. 0 \<le> j \<and> j < i \<longrightarrow> semantics_mltl (drop j \<pi>) F1))"
          if sem: "(semantics_mltl \<pi> F2 \<or> (semantics_mltl \<pi> F1 \<and>
          (\<exists>i. (0 \<le> i \<and> i \<le> b - 1) \<and> semantics_mltl (drop (i+1) \<pi>) F2 \<and>
          (\<forall>j. 0 \<le> j \<and> j < i \<longrightarrow> semantics_mltl (drop (j + 1) \<pi>) F1))))"
        proof - 
          {assume *: "semantics_mltl \<pi> F2"
            then have "semantics_mltl (drop 0 \<pi>) F2 \<and> (\<forall>j. 0 \<le> j \<and> j < 0 \<longrightarrow> semantics_mltl (drop j \<pi>) F1)"
              by simp
            then have ?thesis by blast
          } moreover {assume **: "semantics_mltl \<pi> F1 \<and> (\<exists>i. (0 \<le> i \<and> i \<le> b - 1) \<and>
            semantics_mltl (drop (i+1) \<pi>) F2 \<and> (\<forall>j. 0 \<le> j \<and> j < i \<longrightarrow> semantics_mltl (drop (j + 1) \<pi>) F1))"
            then obtain i where i_prop: "(0 \<le> i \<and> i \<le> b - 1) \<and> semantics_mltl (drop (i + 1) \<pi>) F2 \<and>
              (\<forall>j. 0 \<le> j \<and> j < i \<longrightarrow> semantics_mltl (drop (j + 1) \<pi>) F1)"
              by auto
            have "semantics_mltl (drop 0 \<pi>) F1"
              using ** by auto
            then have "(0 \<le> i \<and> i \<le> b - 1) \<and> semantics_mltl (drop (i + 1) \<pi>) F2 \<and>
              (\<forall>j. 0 \<le> j \<and> j < i+1 \<longrightarrow> semantics_mltl (drop j \<pi>) F1)"
              using i_prop 
              using less_Suc_eq_0_disj by force
            then have "(0 \<le> (i+1) \<and> (i+1) \<le> b) \<and>
        semantics_mltl (drop (i+1) \<pi>) F2 \<and> (\<forall>j. 0 \<le> j \<and> j < (i+1) \<longrightarrow> semantics_mltl (drop j \<pi>) F1)"
              using * by auto 
            then have ?thesis by blast
          }
          ultimately show ?thesis using sem by auto
        qed

      have d2: "(semantics_mltl \<pi> F2 \<or>
           (semantics_mltl \<pi> F1 \<and>
           (\<exists>i. (0 \<le> i \<and> i \<le> b - 1) \<and> semantics_mltl (drop (i+1) \<pi>) F2 \<and>
                (\<forall>j. 0 \<le> j \<and> j < i \<longrightarrow> semantics_mltl (drop (j + 1) \<pi>) F1))))"
        if i_ex: "(\<exists>i. (0 \<le> i \<and> i \<le> b) \<and>
                semantics_mltl (drop i \<pi>) F2 \<and> (\<forall>j. 0 \<le> j \<and> j < i \<longrightarrow> semantics_mltl (drop j \<pi>) F1))"
      proof - 
        obtain i where i_prop: "(0 \<le> i \<and> i \<le> b) \<and>
                semantics_mltl (drop i \<pi>) F2 \<and> (\<forall>j. 0 \<le> j \<and> j < i \<longrightarrow> semantics_mltl (drop j \<pi>) F1)"
          using i_ex by auto
        {assume *: "i = 0"
          then have "semantics_mltl (drop 0 \<pi>) F2"
            using i_prop
            by auto
          then have "semantics_mltl \<pi> F2"
            by auto
          then have ?thesis by blast           
        } moreover { assume * : "i > 0"
          then have g1: "semantics_mltl \<pi> F1"
            using i_prop by auto
          have i_sem: "(0 \<le> i-1 \<and> i-1 \<le> b) \<and>
            semantics_mltl (drop ((i-1)+1) \<pi>) F2"
            using i_prop * by auto
          have "\<And>j. 0 \<le> j \<and> j < i \<Longrightarrow> semantics_mltl (drop j \<pi>) F1"
            using i_prop
            by auto
          then have "\<And>j. 0 \<le> j \<and> j < i-1 \<Longrightarrow> semantics_mltl (drop (j + 1) \<pi>) F1"
            using i_prop g1 
            by (simp add: less_diff_conv)
          then have g2: "(0 \<le> i-1 \<and> i-1 \<le> b - 1) \<and>
        semantics_mltl (drop (i-1 + 1) \<pi>) F2 \<and>
        (\<forall>j. 0 \<le> j \<and> j < i-1 \<longrightarrow> semantics_mltl (drop (j + 1) \<pi>) F1)"  
            using i_sem  
            using diff_le_mono i_prop by presburger
          have ?thesis using g1 g2 by auto
        }
        ultimately show ?thesis
          by blast
      qed
   
        have "(semantics_mltl \<pi> F2 \<or>
     (semantics_mltl \<pi> F1 \<and>
     (\<exists>i. (0 \<le> i \<and> i \<le> b - 1) \<and> semantics_mltl (drop (i+1) \<pi>) F2 \<and>
          (\<forall>j. 0 \<le> j \<and> j < i \<longrightarrow> semantics_mltl (drop (j + 1) \<pi>) F1)))) =
    ((\<exists>i. (0 \<le> i \<and> i \<le> b) \<and>
          semantics_mltl (drop i \<pi>) F2 \<and> (\<forall>j. 0 \<le> j \<and> j < i \<longrightarrow> semantics_mltl (drop j \<pi>) F1)))"
          using d1 d2 by blast
        then  have "semantics_mltl (drop 1 \<pi>)
     (Or_mltl (formula_progression_len1 F2 (\<pi> ! 0))
                 (And_mltl (formula_progression_len1 F1 (\<pi> ! 0)) (Until_mltl F1 0 (b - 1) F2))
           ) =
    semantics_mltl \<pi> (Until_mltl F1 0 b F2)"
          unfolding semantics_mltl.simps using * Until_mltl
          by auto
        then have ?case unfolding formula_progression_len1.simps using *
          by auto
      }
     moreover {assume *: "\<not>(0 < a \<and> a \<le> b) \<and> \<not>(0 = a \<and> a < b)"
       then have a_eq_b: "a = 0 \<and> b = 0"
         using Until_mltl(4) by auto
       then have same_fm1: "(formula_progression_len1 (Until_mltl F1 0 0 F2) (\<pi> ! 0)) = formula_progression_len1 F2 (\<pi> ! 0)"
         by auto
       have same_fm2: "semantics_mltl \<pi> F2 = semantics_mltl (drop 1 \<pi>) (formula_progression_len1 F2 (\<pi> ! 0))"
         using Until_mltl(2) Until_mltl(3) Until_mltl(4)
         by simp
       have same_fm3: "semantics_mltl \<pi> (Until_mltl F1 0 0 F2) = semantics_mltl \<pi> F2"
         using semantics_mltl.simps(9)[of \<pi> F1 0 0 F2]
         using Until_mltl(3) by auto
       have "semantics_mltl (drop 1 \<pi>) (formula_progression_len1 F2 (\<pi> ! 0)) =  semantics_mltl \<pi> (Until_mltl F1 0 0 F2)"
         using same_fm1 same_fm2 same_fm3 by blast
       then have "semantics_mltl (drop 1 \<pi>) (formula_progression_len1 (Until_mltl F1 0 0 F2) (\<pi> ! 0)) =
          semantics_mltl \<pi> (Until_mltl F1 0 0 F2)"
         using same_fm3 by auto
       then have ?case using a_eq_b by auto
     }
     ultimately show ?case by auto
    next
      case (Release_mltl F1 a b F2)
      {assume * :"0< a \<and> a\<le> b"
        have d1: "(\<forall>i. (a - 1 \<le> i \<and> i \<le> b - 1) \<longrightarrow>
               semantics_mltl (drop i (drop 1 \<pi>)) F2 \<or>
              (\<exists>j. a - 1 \<le> j \<and> j < i \<and> semantics_mltl (drop j (drop 1 \<pi>)) F1))"
          if all_i: "((\<forall>i. a \<le> i \<and> i \<le> b \<longrightarrow> semantics_mltl (drop i \<pi>) F2) \<or>
            (\<exists>j\<ge>a. j \<le> b - 1 \<and> semantics_mltl (drop j \<pi>) F1 \<and>
             (\<forall>k. a \<le> k \<and> k \<le> j \<longrightarrow> semantics_mltl (drop k \<pi>) F2)))"
        proof - 
          {assume or1: "(\<forall>i. a \<le> i \<and> i \<le> b \<longrightarrow> semantics_mltl (drop i \<pi>) F2)"
            then have "(\<forall>i. (a - 1 \<le> i \<and> i \<le> b - 1) \<longrightarrow> semantics_mltl (drop i (drop 1 \<pi>)) F2)"
              using * 
              using le_diff_conv by auto
            then have ?thesis
              by blast
          } moreover {assume or2 : "(\<exists>j\<ge>a. j \<le> b - 1 \<and> semantics_mltl (drop j \<pi>) F1 \<and>
             (\<forall>k. a \<le> k \<and> k \<le> j \<longrightarrow> semantics_mltl (drop k \<pi>) F2))"
            then obtain j where j_prop: "j\<ge>a \<and> j \<le> b - 1 \<and>
         semantics_mltl (drop j \<pi>) F1 \<and> (\<forall>k. a \<le> k \<and> k \<le> j \<longrightarrow> semantics_mltl (drop k \<pi>) F2)"
              by blast
            then have "semantics_mltl (drop i (drop 1 \<pi>)) F2 \<or>
        (\<exists>j\<ge>a - 1. j < i \<and> semantics_mltl (drop j (drop 1 \<pi>)) F1)" 
              if i_prop: "a - 1 \<le> i \<and> i \<le> b - 1" for i
            proof - 
              {assume j: "j-1 < i"
                then have "j-1\<ge>a - 1 \<and> j-1 < i \<and> semantics_mltl (drop (j-1) (drop 1 \<pi>)) F1"
                  using j_prop * by auto
                then have ?thesis  by blast
              } moreover {assume j: "j-1 \<ge> i"
                then have "j \<ge> i+1"
                  using j_prop * by linarith
                then have " semantics_mltl (drop (i+1) \<pi>) F2"
                  using j_prop * 
                  using le_diff_conv that by blast
                then have ?thesis by simp
              }
              ultimately show ?thesis
                by force
          qed
          then have ?thesis by blast
          }
          ultimately show ?thesis using all_i by blast
        qed
        have d2: "((\<forall>i. a \<le> i \<and> i \<le> b \<longrightarrow> semantics_mltl (drop i \<pi>) F2) \<or>
          (\<exists>j\<ge>a. j \<le> b - 1 \<and> semantics_mltl (drop j \<pi>) F1 \<and>
             (\<forall>k. a \<le> k \<and> k \<le> j \<longrightarrow> semantics_mltl (drop k \<pi>) F2)))"
          if i_prop: "(\<And>i. (a - 1 \<le> i \<and> i \<le> b - 1) \<Longrightarrow>
               semantics_mltl (drop i (drop 1 \<pi>)) F2 \<or>
              (\<exists>j. a - 1 \<le> j \<and> j < i \<and> semantics_mltl (drop j (drop 1 \<pi>)) F1))"
        proof - 
          {assume contra: "\<not>(\<forall>i. a \<le> i \<and> i \<le> b \<longrightarrow> semantics_mltl (drop i \<pi>) F2)"
            then have exi: "\<exists>i. a \<le> i \<and> i \<le> b \<and> \<not> (semantics_mltl (drop i \<pi>) F2)"
              by blast
            then obtain i where least_exi:
                  "i = (LEAST j. a \<le> j \<and>j \<le> b \<and> \<not> (semantics_mltl (drop j \<pi>) F2))"
              by blast
            then have least_prop1: "a \<le> i \<and>i \<le> b \<and> \<not> (semantics_mltl (drop i \<pi>) F2)"
              by (metis (no_types, lifting) LeastI \<open>\<exists>i\<ge>a. i \<le> b \<and> \<not> semantics_mltl (drop i \<pi>) F2\<close>)
            have least_prop2: "(semantics_mltl (drop k \<pi>) F2)" if k: "a \<le> k \<and> k < i" for k
              using Least_le exi least_exi k 
              by (smt (z3) linorder_not_less order.asym order_le_less_trans)
            have i_bound: "a - 1 \<le> i - 1 \<and> i - 1 \<le> b - 1"
              using least_prop1 * by auto
            have "\<not> (semantics_mltl (drop (i - 1) (drop 1 \<pi>)) F2)"
              using least_prop1 * by auto
            then have "\<exists>j. a - 1 \<le> j \<and> j < i-1 \<and> semantics_mltl (drop (j+1) \<pi>) F1"
              using i_prop[OF i_bound] by simp
            then obtain j where " a - 1 \<le> j \<and> j < i-1 \<and> semantics_mltl (drop (j+1) \<pi>) F1"
              by auto
            then have "j+1 \<ge> a \<and> j+1 \<le> b - 1 \<and> semantics_mltl (drop (j+1) \<pi>) F1 \<and>
             (\<forall>k. a \<le> k \<and> k \<le> (j+1) \<longrightarrow> semantics_mltl (drop k \<pi>) F2)"
              using least_prop2 least_prop1
              by (smt (z3) Suc_eq_plus1 Suc_leI le_diff_conv le_imp_less_Suc less_diff_conv order_less_le_trans) 
            then have "(\<exists>j\<ge>a. j \<le> b - 1 \<and> semantics_mltl (drop j \<pi>) F1 \<and>
             (\<forall>k. a \<le> k \<and> k \<le> j \<longrightarrow> semantics_mltl (drop k \<pi>) F2))"
              by blast
          }
          then show ?thesis by blast
        qed
        have "(\<forall>i. (a - 1 \<le> i \<and> i \<le> b - 1) \<longrightarrow>
               semantics_mltl (drop i (drop 1 \<pi>)) F2 \<or>
              (\<exists>j. a - 1 \<le> j \<and> j < i \<and> semantics_mltl (drop j (drop 1 \<pi>)) F1)) =
     ((\<forall>i. a \<le> i \<and> i \<le> b \<longrightarrow> semantics_mltl (drop i \<pi>) F2) \<or>
     (\<exists>j\<ge>a. j \<le> b - 1 \<and>
             semantics_mltl (drop j \<pi>) F1 \<and>
             (\<forall>k. a \<le> k \<and> k \<le> j \<longrightarrow> semantics_mltl (drop k \<pi>) F2)))"
          using d1 d2 by blast
        then have "(\<not> (a - 1 < length (drop 1 \<pi>)) \<or>
         \<not>(\<exists>i. (a - 1 \<le> i \<and> i \<le> b - 1) \<and>
              \<not> semantics_mltl (drop i (drop 1 \<pi>)) F2 \<and>
              (\<forall>j. a - 1 \<le> j \<and> j < i \<longrightarrow> \<not> semantics_mltl (drop j (drop 1 \<pi>)) F1))) =
    (length \<pi> \<le> a \<or>
     (\<forall>i. a \<le> i \<and> i \<le> b \<longrightarrow> semantics_mltl (drop i \<pi>) F2) \<or>
     (\<exists>j\<ge>a. j \<le> b - 1 \<and>
             semantics_mltl (drop j \<pi>) F1 \<and>
             (\<forall>k. a \<le> k \<and> k \<le> j \<longrightarrow> semantics_mltl (drop k \<pi>) F2)))"
          by (smt (verit) "*" One_nat_def Suc_leI assms(1) leD length_drop less_diff_iff linorder_not_less order_less_imp_le)
        then have "(\<not> semantics_mltl (drop 1 \<pi>)
         (Until_mltl (Not_mltl F1) (a - 1) (b - 1) (Not_mltl F2))) =
     (length \<pi> \<le> a \<or>
      (\<forall>i. a \<le> i \<and> i \<le> b \<longrightarrow> semantics_mltl (drop i \<pi>) F2) \<or>
      (\<exists>j\<ge>a. j \<le> b - 1 \<and>
              semantics_mltl (drop j \<pi>) F1 \<and>
              (\<forall>k. a \<le> k \<and> k \<le> j \<longrightarrow> semantics_mltl (drop k \<pi>) F2)))"
          unfolding semantics_mltl.simps 
          using "*" diff_le_mono by presburger
        then have ?case unfolding formula_progression_len1.simps
        semantics_mltl.simps using Release_mltl * 
          by auto
      } moreover {assume * :"0=a \<and> a<b"
        have d1: "(semantics_mltl \<pi> F2 \<and>
               (semantics_mltl \<pi> F1 \<or>
               (\<forall>i. (0 \<le> i \<and> i \<le> b - 1) \<longrightarrow>
                    semantics_mltl (drop (i+1) \<pi>) F2 \<or>
                    (\<exists>j. 0 \<le> j \<and> j < i \<and> semantics_mltl (drop (j+1) \<pi>) F1))))"
          if all_i: "((\<forall>i. 0 \<le> i \<and> i \<le> b \<longrightarrow> semantics_mltl (drop i \<pi>) F2) \<or>
           (\<exists>j\<ge>0. j \<le> b - 1 \<and>
                   semantics_mltl (drop j \<pi>) F1 \<and>
                   (\<forall>k. 0 \<le> k \<and> k \<le> j \<longrightarrow> semantics_mltl (drop k \<pi>) F2)))"
        proof - 
          have F2: "semantics_mltl \<pi> F2"
            using all_i by auto
          {assume **: "(\<forall>i. 0 \<le> i \<and> i \<le> b \<longrightarrow> semantics_mltl (drop i \<pi>) F2)"
            have "(semantics_mltl \<pi> F1 \<or>
               (\<forall>i. (0 \<le> i \<and> i \<le> b - 1) \<longrightarrow>
                    semantics_mltl (drop (i+1) \<pi>) F2 \<or>
                    (\<exists>j. 0 \<le> j \<and> j < i \<and> semantics_mltl (drop (j+1) \<pi>) F1)))"
              using ** 
              by (simp add: "*" Nat.le_diff_conv2 Suc_leI)
            then have ?thesis using F2 by auto
          } moreover {assume ** : " (\<exists>j\<ge>0. j \<le> b - 1 \<and>
                   semantics_mltl (drop j \<pi>) F1 \<and>
                   (\<forall>k. 0 \<le> k \<and> k \<le> j \<longrightarrow> semantics_mltl (drop k \<pi>) F2))"
            then obtain j where j_prop: "0\<le> j \<and> j \<le> b - 1 \<and>
                   semantics_mltl (drop j \<pi>) F1 \<and>
                   (\<forall>k. 0 \<le> k \<and> k \<le> j \<longrightarrow> semantics_mltl (drop k \<pi>) F2)"
              by auto
            {assume * :"j = 0"
                then have "(semantics_mltl \<pi> F1 \<or>
               (\<forall>i. (0 \<le> i \<and> i \<le> b - 1) \<longrightarrow>
                    semantics_mltl (drop (i+1) \<pi>) F2 \<or>
                    (\<exists>j. 0 \<le> j \<and> j < i \<and> semantics_mltl (drop (j+1) \<pi>) F1)))"
                  using j_prop by simp
            } moreover {assume * :"j > 0"
                then have " (\<forall>i. (0 \<le> i \<and> i \<le> b - 1) \<longrightarrow>
                    semantics_mltl (drop (i+1) \<pi>) F2 \<or>
                    (\<exists>j. 0 \<le> j \<and> j < i \<and> semantics_mltl (drop (j+1) \<pi>) F1))"
                  using j_prop
                  by (metis Nat.le_imp_diff_is_add le0 less_diff_conv less_one linorder_le_less_linear nat_less_le) 
            }
            ultimately have "(semantics_mltl \<pi> F1 \<or>
               (\<forall>i. (0 \<le> i \<and> i \<le> b - 1) \<longrightarrow>
                    semantics_mltl (drop (i+1) \<pi>) F2 \<or>
                    (\<exists>j. 0 \<le> j \<and> j < i \<and> semantics_mltl (drop (j+1) \<pi>) F1)))"
              using j_prop by blast
            then have ?thesis using F2 by auto
          }
          ultimately show ?thesis using all_i
            by blast
        qed

        have d2: "((\<forall>i. 0 \<le> i \<and> i \<le> b \<longrightarrow> semantics_mltl (drop i \<pi>) F2) \<or>
           (\<exists>j\<ge>0. j \<le> b - 1 \<and>
                   semantics_mltl (drop j \<pi>) F1 \<and>
                   (\<forall>k. 0 \<le> k \<and> k \<le> j \<longrightarrow> semantics_mltl (drop k \<pi>) F2)))"
          if all_i: "(semantics_mltl \<pi> F2 \<and>
               (semantics_mltl \<pi> F1 \<or>
               (\<forall>i. (0 \<le> i \<and> i \<le> b - 1) \<longrightarrow>
                    semantics_mltl (drop (i+1) \<pi>) F2 \<or>
                    (\<exists>j. 0 \<le> j \<and> j < i \<and> semantics_mltl (drop (j+1) \<pi>) F1))))"
        proof - 
          have F2: "semantics_mltl \<pi> F2"
            using all_i by auto
          {assume **: "semantics_mltl \<pi> F1"
            then have "0 \<le> b - 1 \<and>
                   semantics_mltl (drop 0 \<pi>) F1 \<and>
                   (\<forall>k. 0 \<le> k \<and> k \<le> 0 \<longrightarrow> semantics_mltl (drop k \<pi>) F2)"
              using F2 * by simp
            then have ?thesis by blast
          } moreover {assume **: " (\<forall>i. (0 \<le> i \<and> i \<le> b - 1) \<longrightarrow>
                    semantics_mltl (drop (i+1) \<pi>) F2 \<or>
                    (\<exists>j. 0 \<le> j \<and> j < i \<and> semantics_mltl (drop (j+1) \<pi>) F1))"
            {assume contra: "\<exists>i. 0 \<le> i \<and> i \<le> b \<and> \<not> (semantics_mltl (drop i \<pi>) F2) \<and>
    \<not>(\<exists>j\<ge>0. j \<le> b - 1 \<and>
            semantics_mltl (drop j \<pi>) F1 \<and>
            (\<forall>k. 0 \<le> k \<and> k \<le> j \<longrightarrow> semantics_mltl (drop k \<pi>) F2))"
              then have "\<not>(\<exists>j\<ge>0. j \<le> b - 1 \<and>
            semantics_mltl (drop j \<pi>) F1 \<and>
            (\<forall>k. 0 \<le> k \<and> k \<le> j \<longrightarrow> semantics_mltl (drop k \<pi>) F2))"
                by meson
              then have all_j: "(\<And>j. (j \<ge> 0 \<and> j \<le> b - 1) \<Longrightarrow>
            \<not> (semantics_mltl (drop j \<pi>) F1) \<or>
            (\<exists>k. 0 \<le> k \<and> k \<le> j \<and> \<not>(semantics_mltl (drop k \<pi>) F2)))"
                by blast
              obtain i where least_i: "i = (LEAST j. 0 \<le> j \<and> j \<le> b \<and> \<not> (semantics_mltl (drop j \<pi>) F2))"
                using contra 
                by auto
              then have least_i1:"0 \<le> i \<and> i \<le> b \<and> \<not> (semantics_mltl (drop i \<pi>) F2)"
                using least_i
                by (metis (no_types, lifting) LeastI contra)
              have least_i2: "\<And>j. 0 \<le> j \<and> j < i \<longrightarrow> (semantics_mltl (drop j \<pi>) F2)" 
                using least_i 
                by (smt (z3) Least_le least_i1 dual_order.strict_iff_order dual_order.trans linorder_not_less)

            
              {assume i_zer: "i = 0"
                then have "False"
                  using F2 least_i1
                  by auto
              } moreover {assume i_zer: "i > 0"
                then have i_bound: "0 \<le> i-1 \<and> i-1 \<le> b - 1"
                  using least_i1
                  by auto
                then have "semantics_mltl (drop i \<pi>) F2 \<or> (\<exists>j\<ge>0. j < i-1 \<and> semantics_mltl (drop (j + 1) \<pi>) F1)"
                  using ** 
                  by (metis One_nat_def Suc_leI i_zer le_add_diff_inverse2) 
                then have "(\<exists>j\<ge>0. j < i - 1 \<and> semantics_mltl (drop (j + 1) \<pi>) F1)"
                  using least_i1 by auto
                then obtain j where j_bounds: "j \<ge> 0 \<and> j < i - 1 \<and> semantics_mltl (drop (j + 1) \<pi>) F1"
                  by auto
                have "(\<exists>k. 0 \<le> k \<and> k \<le> (j+1) \<and> \<not>(semantics_mltl (drop k \<pi>) F2))"
                  using all_j j_bounds i_bound by auto
                then obtain k where "0 \<le> k \<and> k \<le> (j+1) \<and> \<not>(semantics_mltl (drop k \<pi>) F2)"
                  by blast
                
                then have "False"
                  using j_bounds least_i2 i_bound ** F2
                  by (meson less_diff_conv order_le_less_trans) 
              }
              ultimately have "False" by auto
            }
            then have ?thesis  by blast
          }
          ultimately show ?thesis using all_i by blast
        qed

      have "(semantics_mltl \<pi> F2 \<and>
               (semantics_mltl \<pi> F1 \<or>
               (\<forall>i. (0 \<le> i \<and> i \<le> b - 1) \<longrightarrow>
                    semantics_mltl (drop (i+1) \<pi>) F2 \<or>
                    (\<exists>j. 0 \<le> j \<and> j < i \<and> semantics_mltl (drop (j+1) \<pi>) F1)))) =
          ((\<forall>i. 0 \<le> i \<and> i \<le> b \<longrightarrow> semantics_mltl (drop i \<pi>) F2) \<or>
           (\<exists>j\<ge>0. j \<le> b - 1 \<and>
                   semantics_mltl (drop j \<pi>) F1 \<and>
                   (\<forall>k. 0 \<le> k \<and> k \<le> j \<longrightarrow> semantics_mltl (drop k \<pi>) F2)))"
        using d1 d2 by blast
        then have "(\<not> (\<not> semantics_mltl \<pi> F2 \<or>
         \<not> semantics_mltl \<pi> F1 \<and>
         0 \<le> b - 1 \<and>
         0 < length (drop 1 \<pi>) \<and>
         (\<exists>i. (0 \<le> i \<and> i \<le> b - 1) \<and>
              \<not> semantics_mltl (drop i (drop 1 \<pi>)) F2 \<and>
              (\<forall>j. 0 \<le> j \<and> j < i \<longrightarrow> \<not> semantics_mltl (drop j (drop 1 \<pi>)) F1)))) =
    ((\<forall>i. 0 \<le> i \<and> i \<le> b \<longrightarrow> semantics_mltl (drop i \<pi>) F2) \<or>
     (\<exists>j\<ge>0. j \<le> b - 1 \<and>
             semantics_mltl (drop j \<pi>) F1 \<and>
             (\<forall>k. 0 \<le> k \<and> k \<le> j \<longrightarrow> semantics_mltl (drop k \<pi>) F2)))"
          using * assms(1) by auto
        then have "(\<not> semantics_mltl (drop 1 \<pi>)
         (Or_mltl (Not_mltl (formula_progression_len1 F2 (\<pi> ! 0)))
                     (And_mltl (Not_mltl (formula_progression_len1 F1 (\<pi> ! 0)))
                       (Until_mltl (Not_mltl F1) 0 (b - 1) (Not_mltl F2))))) =
    ((\<forall>i. 0 \<le> i \<and> i \<le> b \<longrightarrow> semantics_mltl (drop i \<pi>) F2) \<or>
      (\<exists>j\<ge>0. j \<le> b - 1 \<and>
              semantics_mltl (drop j \<pi>) F1 \<and>
              (\<forall>k. 0 \<le> k \<and> k \<le> j \<longrightarrow> semantics_mltl (drop k \<pi>) F2)))"
          unfolding semantics_mltl.simps using Release_mltl * 
          by auto
        then have ?case using Release_mltl unfolding formula_progression_len1.simps
        semantics_mltl.simps using Release_mltl *
          by auto
      }
      moreover {assume * :"\<not>(0< a \<and> a\<le> b) \<and> \<not> (0=a \<and> a<b)"
        then have **: "a = b \<and> b = 0"
          using Release_mltl(4) by auto 
        then have "semantics_mltl \<pi> F2 =
          (length \<pi> \<le> a \<or>
          (\<forall>i. 0 \<le> i \<and> i \<le> 0 \<longrightarrow> semantics_mltl (drop i \<pi>) F2))" 
          using assms(1) by auto
        then have "semantics_mltl \<pi> F2 =
          (length \<pi> \<le> a \<or>
          (\<forall>i. 0 \<le> i \<and> i \<le> 0 \<longrightarrow> semantics_mltl (drop i \<pi>) F2) \<or>
          (\<exists>j\<ge>0. j \<le> 0 - 1 \<and>
                semantics_mltl (drop j \<pi>) F1 \<and>
                (\<forall>k. a \<le> k \<and> k \<le> j \<longrightarrow> semantics_mltl (drop k \<pi>) F2)))"
          using "**" by force
        then have ?case unfolding formula_progression_len1.simps
        semantics_mltl.simps using Release_mltl ** by auto
    }
      ultimately show ?case by blast
    qed

text \<open> Theorem 2 \<close>
theorem satisfiability_preservation:
  fixes \<phi>::"'a mltl"
  assumes "k \<ge> 1"
  assumes "k < length \<pi>"
  assumes "intervals_welldef \<phi>"
  shows "semantics_mltl (drop k \<pi>) (formula_progression \<phi> (take k \<pi> ))
    \<longleftrightarrow> semantics_mltl \<pi> \<phi>"
  using assms
proof (induct k  arbitrary: \<pi> \<phi> rule: less_induct)
  case (less k)
  {assume *: "k = 1"
    then have "semantics_mltl (drop 1 \<pi>) (formula_progression_len1 \<phi> (\<pi> ! 0))
    \<longleftrightarrow> semantics_mltl \<pi> \<phi>"
      using satisfiability_preservation_len1 less
      by blast
    then have ?case using * less unfolding formula_progression_len1.simps 
      by simp
  } moreover {assume *: "k > 1"
    let ?tr = "(drop (k-1) \<pi>)"
    let ?fm = "formula_progression \<phi> (take (k-1) \<pi> )"
    let ?tr1 = "(drop k \<pi>)"
    let ?fm1 = "formula_progression ?fm [\<pi> ! (k-1)]"
    have  "semantics_mltl ?tr ?fm  \<longleftrightarrow> semantics_mltl \<pi> \<phi>"
      using less * by auto
    have drop_id: "drop 1 (drop (k - 1) \<pi>) = ?tr1"
      using *
      by auto
    have take_id: "take 1 (drop (k - 1) \<pi>) = [\<pi> ! (k-1)]"
      using * less(3)
      by (metis Cons_nth_drop_Suc One_nat_def diff_less dual_order.strict_trans less_numeral_extra(1) take0 take_Suc_Cons) 
    have ind_welldef:  " intervals_welldef (formula_progression \<phi> (take (k - 1) \<pi>))"
      using less(4) formula_progression_well_definedness_preserved[of \<phi> "(take (k - 1) \<pi>)"]
      by blast
    have "1 < length (drop (k - 1) \<pi>)"
      using less * by auto
    then have same_sem: "semantics_mltl ?tr ?fm  \<longleftrightarrow>  semantics_mltl ?tr1 ?fm1"
      using less(1)[of 1 ?tr ?fm] * drop_id take_id ind_welldef
      by auto
    have "?fm1 = formula_progression \<phi> (take k \<pi> )"
      using formula_progression_decomposition[of "k-1" "take k \<pi>"] * less *
      by simp
    then have ?case 
      using same_sem 
      using \<open>semantics_mltl (drop (k - 1) \<pi>) (formula_progression \<phi> (take (k - 1) \<pi>)) = semantics_mltl \<pi> \<phi>\<close> by presburger
  }
  ultimately show ?case
    using less
    by auto
qed

paragraph \<open>Counter example to Theorem 2 showing how the theorem can fail if
the trace length condition is removed.\<close>

lemma theorem2_cexa:
  fixes \<phi>::"nat mltl"
  assumes "k = 1"
  assumes "\<pi> = [{1::nat}]"
  assumes "\<phi> = G\<^sub>m [0,3] (Prop_mltl (1::nat))"
  assumes "intervals_welldef \<phi>"
  shows "(drop k \<pi>) \<Turnstile>\<^sub>m (formula_progression \<phi> (take k \<pi>)) = True" 
  using assms unfolding semantics_mltl.simps by auto

value "(take 1 [{1::nat}])"
value "formula_progression (G\<^sub>m [0,3] (Prop_mltl (1::nat))) (take 1 [{1::nat}])"


lemma theorem2_cexb:
  fixes \<phi>::"nat mltl"
  assumes "\<pi> = [{1::nat}]"
  assumes "\<phi> = G\<^sub>m [0,1] (Prop_mltl (1::nat))"
  assumes "intervals_welldef \<phi>"
  shows "semantics_mltl \<pi> \<phi> = False" 
  using assms unfolding semantics_mltl.simps assms
  by auto


subsubsection \<open>Theorem 3\<close>

paragraph \<open>Setup: Properties of Computation Length\<close>

lemma complen_geq_1:
  shows "complen_mltl \<phi> \<ge> 1"
  apply (induction \<phi>) by simp_all

text \<open> This is a key property that makes the base case of Theorem 3 work:
   Constraining the computation length of the formula means that
   the formula progression is either globally true or false.
   This is a very strong structural property that lets us use the
   inductive hypotheses in, e.g., the Or case and the Not case of 
   the base case of Theorem 3. \<close>
lemma complen_bounded_by_1:
  assumes "intervals_welldef \<phi>"
  assumes "1 \<ge> complen_mltl \<phi>"
  shows "(\<forall>\<xi>. \<xi> \<Turnstile>\<^sub>m(formula_progression_len1 \<phi> \<pi>)) \<or> 
         (\<forall>\<xi>. \<not> (\<xi> \<Turnstile>\<^sub>m (formula_progression_len1 \<phi> \<pi>)))"
  using assms
proof (induct \<phi> arbitrary: \<pi>)
  case True_mltl
  then show ?case
    by auto
next
  case False_mltl
  then show ?case by auto
next
  case (Prop_mltl x)
  then show ?case by simp
next
  case (Not_mltl \<phi>)
  then show ?case by auto
next
  case (And_mltl \<phi>1 \<phi>2)
  then show ?case by auto
next
  case (Or_mltl \<phi>1 \<phi>2)
  then show ?case by auto
next
  case (Future_mltl \<phi> a b)
  then show ?case 
    using One_nat_def add_diff_cancel_left' add_diff_cancel_right' complen_geq_one complen_mltl.simps(8) formula_progression_len1.simps(10) le_add2 less_numeral_extra(3) nle_le order_less_le_trans plus_1_eq_Suc
    by (metis intervals_welldef.simps(7))
next
  case (Global_mltl \<phi> a b)
  then show ?case
    by (metis (no_types, lifting) One_nat_def add_diff_cancel_left' add_diff_cancel_right' complen_geq_one complen_mltl.simps(7) formula_progression_len1.simps(10) formula_progression_len1.simps(4) formula_progression_len1.simps(9) intervals_welldef.simps(8) le_add2 less_numeral_extra(3) nle_le plus_1_eq_Suc semantics_mltl.simps(4) zero_le) 
next
  case (Until_mltl \<phi>1 a b \<phi>2)
  have "max (complen_mltl \<phi>1 - 1) (complen_mltl \<phi>2) \<ge> 1"
    using complen_geq_1 
    using max.coboundedI2 by blast
  then have "a = 0 \<and> b = 0"
    using Until_mltl(4) complen_geq_1 unfolding complen_mltl.simps 
    by (metis Until_mltl.prems(1) add_cancel_right_left add_leD2 complen_mltl.simps(10) intervals_welldef.simps(9) le_antisym le_zero_eq)
  then show ?case 
    using Until_mltl
    by simp
next
  case (Release_mltl \<phi>1 a b \<phi>2)
   have "max (complen_mltl \<phi>1 - 1) (complen_mltl \<phi>2) \<ge> 1"
    using complen_geq_1 
    using max.coboundedI2 by blast
  then have "a = 0 \<and> b = 0"
    using Release_mltl(4) unfolding complen_mltl.simps
    by (metis Release_mltl.prems(1) add_diff_cancel_right' add_leD2 diff_is_0_eq' intervals_welldef.simps(10) le_antisym le_zero_eq) 
  then show ?case 
    using Release_mltl
    by simp
qed

lemma complen_temporal_props:
  shows "(complen_mltl (F\<^sub>m [a,b] \<phi>) = 1 \<Longrightarrow> (b = 0))"
        "(complen_mltl (G\<^sub>m [a,b] \<phi>)  = 1 \<Longrightarrow> (b = 0))"
        "(complen_mltl (\<phi>1 U\<^sub>m [a,b] \<phi>2)  = 1 \<Longrightarrow> (b = 0))"
        "(complen_mltl (\<phi>1 R\<^sub>m [a,b] \<phi>2)  = 1 \<Longrightarrow> (b = 0))"
proof - 
  assume "complen_mltl (F\<^sub>m [a,b] \<phi>) = 1"
  then show "b = 0"
    unfolding complen_mltl.simps using complen_geq_1
    by (metis add_le_same_cancel2 le_zero_eq)
  next assume "complen_mltl (G\<^sub>m [a,b] \<phi>)  = 1"
    then show "b = 0"
    unfolding complen_mltl.simps using complen_geq_1
    by (metis add_le_same_cancel2 le_zero_eq)
  next assume "complen_mltl (\<phi>1 U\<^sub>m [a,b] \<phi>2) = 1"
  then show "b = 0"
    unfolding complen_mltl.simps using complen_geq_1
    by (metis add_le_same_cancel2 le_zero_eq max.coboundedI2)
  next assume "complen_mltl (\<phi>1 R\<^sub>m [a,b] \<phi>2) = 1"
  then show "b = 0"
    unfolding complen_mltl.simps using complen_geq_1
    by (metis One_nat_def add_is_1 max_nat.eq_neutr_iff not_one_le_zero)
qed

lemma complen_one_implies_one_base:
  assumes "intervals_welldef \<phi>"
  assumes "complen_mltl \<phi> = 1"
  shows "complen_mltl (formula_progression_len1 \<phi> k) = 1"
  using assms
proof (induct \<phi>)
  case True_mltl
  then show ?case by simp
next
  case False_mltl
  then show ?case by simp
next
  case (Prop_mltl x)
  then show ?case by simp
next
  case (Not_mltl \<phi>)
  then show ?case by simp
next
  case (And_mltl \<phi>1 \<phi>2)
  then show ?case using complen_geq_1 
    unfolding formula_progression_len1.simps
    by (metis (full_types) complen_mltl.simps(5) intervals_welldef.simps(5) max.absorb1 max_def) 
next
  case (Or_mltl \<phi>1 \<phi>2)
  then show ?case using complen_geq_1 
    unfolding formula_progression_len1.simps intervals_welldef.simps(6)
    by (metis complen_mltl.simps(6) max.cobounded1 max.cobounded2 nle_le)
next
  case (Future_mltl a b \<phi>)
  then have "a = 0 \<and> b = 0"
    using complen_temporal_props(1)[of a b \<phi>]
    unfolding intervals_welldef.simps by simp
  then show ?case
    by (metis Future_mltl.hyps Future_mltl.prems(1) Future_mltl.prems(2) One_nat_def add_diff_cancel_left' add_diff_cancel_right' complen_mltl.simps(8) formula_progression_len1.simps(10) intervals_welldef.simps(7) less_numeral_extra(3) plus_1_eq_Suc) 
next
  case (Global_mltl a b \<phi>)
  then have "a = 0 \<and> b = 0"
    using complen_temporal_props(2)[of a b \<phi>]
    unfolding intervals_welldef.simps by simp
  then show ?case
    using Global_mltl.hyps Global_mltl.prems(1) Global_mltl.prems(2) by auto 
next
  case (Until_mltl \<phi>1 a b \<phi>2)
  then have "a = 0 \<and> b = 0"
    using complen_temporal_props(3)[of \<phi>1 a b \<phi>2]
    unfolding intervals_welldef.simps by simp
  then show ?case
    by (metis One_nat_def Until_mltl.hyps(2) Until_mltl.prems(1) Until_mltl.prems(2) add_diff_cancel_left' add_diff_cancel_right' complen_geq_1 complen_mltl.simps(10) formula_progression_len1.simps(7) intervals_welldef.simps(9) le_antisym less_numeral_extra(3) max.bounded_iff plus_1_eq_Suc) 
next
  case (Release_mltl \<phi>1 a b \<phi>2)
  then have "a = 0 \<and> b = 0"
    using complen_temporal_props(4)[of \<phi>1 a b \<phi>2]
    unfolding intervals_welldef.simps by simp
  then show ?case
    by (metis (no_types, lifting) One_nat_def Release_mltl.hyps(2) Release_mltl.prems(1) Release_mltl.prems(2) add_diff_cancel_left' add_diff_cancel_right' complen_geq_1 complen_mltl.simps(4) complen_mltl.simps(9) formula_progression_len1.simps(4) formula_progression_len1.simps(7) formula_progression_len1.simps(8) intervals_welldef.simps(10) less_numeral_extra(3) max_def plus_1_eq_Suc)
qed

lemma complen_one_implies_one:
  assumes "intervals_welldef \<phi>"
  assumes "complen_mltl \<phi> = 1"
  shows "complen_mltl (formula_progression \<phi> \<pi>) = 1"
  using assms
proof (induct "length \<pi>" arbitrary: \<pi> \<phi>)
  case 0
  then show ?case by auto
next
  case (Suc x)
  {assume *: "x = 0"
    then have ?case
      using complen_one_implies_one_base
      Suc
      by (metis One_nat_def formula_progression.elims)
  } moreover {assume *: "x > 0"
    then have "complen_mltl (formula_progression (formula_progression_len1 \<phi> (\<pi> ! 0))
                (drop 1 \<pi>)) = 1"
      using complen_one_implies_one_base[OF Suc(3) Suc(4), of "\<pi> ! 0"] Suc(1)[of "(drop 1 \<pi>)" "formula_progression_len1 \<phi> (\<pi> ! 0)"]
      formula_progression_well_definedness_preserved_len1[of \<phi> "\<pi> ! 0"]
      by (metis Suc.hyps(2) Suc.prems(1) diff_Suc_1 length_drop)
    then have ?case  
      using formula_progression.simps[of \<phi> \<pi>] using Suc * 
      by auto
  }
  ultimately show ?case by blast
qed
 
lemma formula_progression_decreases_complen_base:
  assumes "intervals_welldef \<phi>"
  shows "complen_mltl \<phi> = 1 \<or> complen_mltl (formula_progression_len1 \<phi> k) \<le> complen_mltl \<phi> - 1"
  using assms
proof (induct \<phi>)
  case True_mltl
  then show ?case
    by simp
next
  case False_mltl
  then show ?case by simp
next
  case (Prop_mltl x)
  then show ?case by simp
next
  case (Not_mltl \<phi>)
  then show ?case by simp
next
  case (And_mltl \<phi>1 \<phi>2)
  {assume * :"complen_mltl \<phi>1 = 1"
    {assume ** :"complen_mltl \<phi>2 = 1"
      then have ?case
        unfolding complen_mltl.simps using *
        by auto
    } moreover {assume ** : "complen_mltl \<phi>2 >1 \<and> complen_mltl (formula_progression_len1 \<phi>2 k) \<le> complen_mltl \<phi>2 - 1"
      then have ?case
        unfolding complen_mltl.simps formula_progression_len1.simps using * complen_one_implies_one_base
        by (metis And_mltl.prems complen_geq_1 intervals_welldef.simps(5) max_def)
    }
    ultimately have ?case
      using And_mltl by fastforce
  }
  moreover {assume * : "complen_mltl \<phi>1 > 1 \<and> complen_mltl (formula_progression_len1 \<phi>1 k) \<le> complen_mltl \<phi>1 - 1"
    {assume ** :"complen_mltl \<phi>2 = 1"
      then have ?case
        unfolding complen_mltl.simps using * 
        by (metis (no_types, lifting) And_mltl.prems complen_geq_1 complen_mltl.simps(5) complen_one_implies_one_base formula_progression_len1.simps(5) intervals_welldef.simps(5) max.absorb1)
    } moreover {assume ** : "complen_mltl \<phi>2 >1 \<and> complen_mltl (formula_progression_len1 \<phi>2 k) \<le> complen_mltl \<phi>2 - 1"
      then have ?case
        unfolding complen_mltl.simps formula_progression_len1.simps using * complen_one_implies_one_base
        by (smt (z3) Nat.le_diff_conv2 complen_geq_1 max.coboundedI2 max.commute max_def)
    }
    ultimately have ?case using And_mltl 
      by (metis complen_geq_1 intervals_welldef.simps(5) order_le_imp_less_or_eq)
  }
  ultimately show ?case using And_mltl
    by (metis complen_geq_1 intervals_welldef.simps(5) order_le_imp_less_or_eq) 
next
  case (Or_mltl \<phi>1 \<phi>2)
{assume * :"complen_mltl \<phi>1 = 1"
    {assume ** :"complen_mltl \<phi>2 = 1"
      then have ?case
        unfolding complen_mltl.simps using *
        by auto
    } moreover {assume ** : "complen_mltl \<phi>2 >1 \<and> complen_mltl (formula_progression_len1 \<phi>2 k) \<le> complen_mltl \<phi>2 - 1"
      then have ?case
        unfolding complen_mltl.simps formula_progression_len1.simps using * complen_one_implies_one_base
        by (metis Or_mltl.prems complen_geq_1 intervals_welldef.simps(6) max_def)
    }
    ultimately have ?case
      using Or_mltl by fastforce
  }
  moreover {assume * : "complen_mltl \<phi>1 > 1 \<and> complen_mltl (formula_progression_len1 \<phi>1 k) \<le> complen_mltl \<phi>1 - 1"
    {assume ** :"complen_mltl \<phi>2 = 1"
      then have ?case
        unfolding complen_mltl.simps using * 
        by (metis (no_types, lifting) Or_mltl.prems complen_geq_1 complen_mltl.simps(6) complen_one_implies_one_base formula_progression_len1.simps(6) intervals_welldef.simps(6) max.absorb1)
    } moreover {assume ** : "complen_mltl \<phi>2 >1 \<and> complen_mltl (formula_progression_len1 \<phi>2 k) \<le> complen_mltl \<phi>2 - 1"
      then have ?case
        unfolding complen_mltl.simps formula_progression_len1.simps using * complen_one_implies_one_base
        by (smt (z3) Nat.le_diff_conv2 complen_geq_1 max.coboundedI2 max.commute max_def)
    }
    ultimately have ?case using Or_mltl 
      by (metis complen_geq_1 intervals_welldef.simps(6) order_le_imp_less_or_eq)
  }
  ultimately show ?case using Or_mltl
    by (metis complen_geq_1 intervals_welldef.simps(6) order_le_imp_less_or_eq) 
next
  case (Future_mltl a b \<phi>)
  {assume *: "complen_mltl \<phi> = 1"
    have iwd: "intervals_welldef \<phi>"
      using Future_mltl(2) by simp
    have a_leq_b: "a\<le>b"
      using Future_mltl
      by auto
    {assume **: "b = 0"
      then have ?case
        using * complen_one_implies_one_base[OF iwd *] 
      unfolding complen_mltl.simps by auto }
  moreover {assume **: "b > 0"
    have complen_not_dec: "complen_mltl (formula_progression_len1 \<phi> p) = 1" for p
      using complen_one_implies_one_base[OF iwd *]  by auto
    {assume ***: " 0 = a"
      then have "(formula_progression_len1 (Future_mltl a b \<phi>) k)
          = (Or_mltl (formula_progression_len1 \<phi> k) (Future_mltl 0 (b - 1) \<phi>))"
        unfolding formula_progression_len1.simps
        using ** * by auto
      then have "complen_mltl (formula_progression_len1 (Future_mltl a b \<phi>) k) = b"
        using * complen_not_dec **
        by auto
      then have ?case unfolding complen_mltl.simps using * 
        by simp
    } moreover {assume ***: "a > 0"
      then have "(formula_progression_len1 (Future_mltl a b \<phi>) k)
          = Future_mltl (a - 1) (b - 1) \<phi>"
        unfolding formula_progression_len1.simps
        using ** * a_leq_b
        by auto
      then have "complen_mltl (formula_progression_len1 (Future_mltl a b \<phi>) k)
          = b"
        using * **
        by simp
      then have ?case unfolding complen_mltl.simps using * 
        by auto
    }
    ultimately have ?case
      by blast
  }
  (* Note: there is a shorter proof here, but it is less clear than the longer proof above. *)
      (*using complen_one_implies_one_base[OF iwd *] 
      unfolding complen_mltl.simps formula_progression_len1.simps
      by (smt (verit) "*" Nat.diff_add_assoc2 Nat.le_imp_diff_is_add One_nat_def complen_mltl.simps(6) complen_mltl.simps(8) formula_progression_len1.simps(10) le_simps(3) max_absorb2 order_class.order_eq_iff) *) 
   ultimately have ?case
     by blast
  } moreover 
  {assume *:"complen_mltl (formula_progression_len1 \<phi> k) \<le> complen_mltl \<phi> - 1"
    then have ?case unfolding complen_mltl.simps formula_progression_len1.simps
      by auto
  }
  ultimately show ?case 
    using Future_mltl by fastforce
next
  case (Global_mltl a b \<phi>)
  have a_leq_b: "a\<le>b"
      using Global_mltl
      by auto
  {assume *: "complen_mltl \<phi> = 1"
    have iwd: "intervals_welldef \<phi>"
      using Global_mltl(2) by simp
    {assume **: "b = 0"
      then have ?case
        using * complen_one_implies_one_base[OF iwd *] 
      unfolding complen_mltl.simps by auto
  }
  moreover {assume **: "b > 0"
    have complen_1: "complen_mltl (Future_mltl (a - 1) (b - 1) (Not_mltl \<phi>)) \<le> b"
      unfolding complen_mltl.simps using * **
      by auto
    have complen_2: "complen_mltl (Or_mltl (Not_mltl (formula_progression_len1 \<phi> k))
                 (Future_mltl 0 (b - 1) (Not_mltl \<phi>))) \<le> b"
      unfolding complen_mltl.simps using * ** complen_one_implies_one_base[OF iwd *] 
      by simp
    then have "complen_mltl (formula_progression_len1 (Future_mltl a b (Not_mltl \<phi>)) k) \<le> b"
      unfolding formula_progression_len1.simps 
      using complen_1 complen_2 ** a_leq_b by simp
    then have "complen_mltl (Not_mltl (formula_progression_len1 (Future_mltl a b (Not_mltl \<phi>)) k)) \<le> b + complen_mltl \<phi> - 1"
      using complen_one_implies_one_base[OF iwd *] 
      unfolding complen_mltl.simps using * by auto
    (* NOTE: there is a shorter proof here, but it is less clear*)
    then have ?case
      using formula_progression_len1.simps(9)
      by simp
  }
   ultimately have ?case
     by blast
  } moreover 
  {assume *:"complen_mltl (formula_progression_len1 \<phi> k) \<le> complen_mltl \<phi> - 1"
    then have ?case unfolding complen_mltl.simps formula_progression_len1.simps
      by auto
  }
  ultimately show ?case 
    using Global_mltl by fastforce
next
  case (Until_mltl \<phi>1 a b \<phi>2)
  {assume *: "complen_mltl \<phi>1 = 1 \<and> complen_mltl \<phi>2 = 1"
    {assume **: "b = 0"
      then have ?case
        unfolding complen_mltl.simps  formula_progression_len1.simps
        using * by auto
    } moreover {assume **: "b > 0"
      then have ?case
        unfolding complen_mltl.simps  formula_progression_len1.simps
        using * 
        by (smt (verit) Nat.diff_diff_right Until_mltl(3) complen_mltl.simps(10) complen_mltl.simps(5) complen_mltl.simps(6) complen_one_implies_one_base diff_is_0_eq' intervals_welldef.simps(9) le_add_diff_inverse2 le_less le_simps(3) minus_nat.diff_0 nat_minus_add_max plus_1_eq_Suc zero_less_one_class.zero_le_one)
        (* May take a second to load *)
    }
    ultimately have ?case
      by blast
  } moreover {assume *: "complen_mltl \<phi>1 = 1 \<and> complen_mltl \<phi>2 > 1 \<and> complen_mltl (formula_progression_len1 \<phi>2 k) \<le> complen_mltl \<phi>2 - 1"
    {assume **: "b = 0"
      then have ?case
        unfolding complen_mltl.simps  formula_progression_len1.simps
        using * by auto
    } moreover {assume **: "b > 0"
      {assume ***: "0 < a \<and> a \<le> b"
        then have "complen_mltl
     ( Until_mltl \<phi>1 (a - 1) (b - 1) \<phi>2)
    \<le> b + max (complen_mltl \<phi>1 - 1) (complen_mltl \<phi>2) - 1"
          using * ** by simp
      } moreover {assume ***: "0 = a \<and> a < b"
        have lt1: " (complen_mltl (formula_progression_len1 \<phi>2 k))
    \<le> b + max (complen_mltl \<phi>1 - 1) (complen_mltl \<phi>2) - 1"
          using * ** by auto
        have complen_not_dec: "complen_mltl (formula_progression_len1 \<phi>1 k) = 1"
          using * complen_one_implies_one_base[of \<phi>1] Until_mltl(3)
          unfolding intervals_welldef.simps by blast
        have lt2: "(max 1 (b - 1 + max 0 (complen_mltl \<phi>2)))
          \<le> b + max 0 (complen_mltl \<phi>2) - 1"
          using * ** by auto
        then have lt2: "(max (complen_mltl (formula_progression_len1 \<phi>1 k))
          (b - 1 + max (complen_mltl \<phi>1 - 1) (complen_mltl \<phi>2)))
          \<le> b + max (complen_mltl \<phi>1 - 1) (complen_mltl \<phi>2) - 1"
          using * complen_not_dec by simp
       (* There is a shorter proof here, but it is less clear. *)
       have "complen_mltl
           (Or_mltl (formula_progression_len1 \<phi>2 k)
                       (And_mltl (formula_progression_len1 \<phi>1 k)
                         (Until_mltl \<phi>1 0 (b - 1) \<phi>2)))
          \<le> b + max (complen_mltl \<phi>1 - 1) (complen_mltl \<phi>2) - 1"
         unfolding complen_mltl.simps formula_progression_len1.simps
         using lt1 lt2
         using max.boundedI by blast
     }
      ultimately have ?case
        unfolding complen_mltl.simps  formula_progression_len1.simps
        using *  by auto 
      }
    ultimately have ?case
      by blast
  }  moreover {assume *: "complen_mltl \<phi>2 = 1 \<and> complen_mltl \<phi>1 > 1 \<and> complen_mltl (formula_progression_len1 \<phi>1 k) \<le> complen_mltl \<phi>1 - 1"
    {assume **: "b = 0"
      then have ?case
        unfolding complen_mltl.simps  formula_progression_len1.simps
        using * 
        using Until_mltl.prems complen_one_implies_one_base by force
    }
    moreover {assume **: "b > 0"
      {assume ***:  "0 < a \<and> a \<le> b"
        then have "b + max (complen_mltl \<phi>1 - 1) (complen_mltl \<phi>2) = 1 \<or>
    complen_mltl
     (Until_mltl \<phi>1 (a - 1) (b - 1) \<phi>2)
    \<le> b + max (complen_mltl \<phi>1 - 1) (complen_mltl \<phi>2) - 1"
          using * ** unfolding complen_mltl.simps 
          by (metis le_refl less_one ordered_cancel_comm_monoid_diff_class.add_diff_assoc2 verit_comp_simplify1(3))
        then have ?case
          using ***
          by auto
      } moreover {assume ***: "0 = a \<and> a < b"
        then have " b + max (complen_mltl \<phi>1 - 1) (complen_mltl \<phi>2) = 1 \<or>
    complen_mltl
     (Or_mltl (formula_progression_len1 \<phi>2 k)
                 (And_mltl (formula_progression_len1 \<phi>1 k)
                   (Until_mltl \<phi>1 0 (b - 1) \<phi>2)))
    \<le> b + max (complen_mltl \<phi>1 - 1) (complen_mltl \<phi>2) - 1"
          using * ** unfolding complen_mltl.simps formula_progression_len1.simps
          by (smt (verit) Nat.add_diff_assoc2 One_nat_def Until_mltl.prems dual_order.eq_iff complen_one_implies_one_base intervals_welldef.simps(9) leD le_add2 max.bounded_iff max_def not_less_eq_eq)
        then have ?case
          using ***
          by auto
      }
      ultimately have ?case
        using *
        using "**" Until_mltl.prems intervals_welldef.simps(9) zero_less_iff_neq_zero by blast 
    }
    ultimately have ?case
      by blast  
  } moreover {assume *: "complen_mltl \<phi>1 > 1 \<and> complen_mltl \<phi>2 > 1 \<and> complen_mltl (formula_progression_len1 \<phi>1 k) \<le> complen_mltl \<phi>1 - 1 \<and> complen_mltl (formula_progression_len1 \<phi>2 k) \<le> complen_mltl \<phi>2 - 1"
    {assume **: "b = 0"
      then have ?case unfolding complen_mltl.simps  formula_progression_len1.simps
        using *
        by (smt (verit, ccfv_threshold) add.commute add_diff_cancel_right' complen_geq_1 diff_diff_left le_zero_eq less_numeral_extra(3) max.cobounded2 nat_minus_add_max order.trans ordered_cancel_comm_monoid_diff_class.add_diff_assoc2) 
    } moreover {assume **: "b > 0"
      {assume ***:  "0 < a \<and> a \<le> b"
        then have "b + max (complen_mltl \<phi>1 - 1) (complen_mltl \<phi>2) = 1 \<or>
    complen_mltl
     (Until_mltl \<phi>1 (a - 1) (b - 1) \<phi>2)
    \<le> b + max (complen_mltl \<phi>1 - 1) (complen_mltl \<phi>2) - 1"
          using * ** unfolding complen_mltl.simps 
          by (metis le_refl less_one ordered_cancel_comm_monoid_diff_class.add_diff_assoc2 verit_comp_simplify1(3))
        then have ?case
          using ***
          by auto
      } moreover {assume ***: "0 = a \<and> a < b"
        then have " b + max (complen_mltl \<phi>1 - 1) (complen_mltl \<phi>2) = 1 \<or>
    complen_mltl
     (Or_mltl (formula_progression_len1 \<phi>2 k)
                 (And_mltl (formula_progression_len1 \<phi>1 k)
                   (Until_mltl \<phi>1 0 (b - 1) \<phi>2)))
    \<le> b + max (complen_mltl \<phi>1 - 1) (complen_mltl \<phi>2) - 1"
         using * ** unfolding complen_mltl.simps formula_progression_len1.simps
         using less_or_eq_imp_le by fastforce
        then have ?case
          using ***
          by auto
      }
      ultimately have ?case
        using *
        using "**" Until_mltl.prems intervals_welldef.simps(9) zero_less_iff_neq_zero by blast 
    }
    ultimately have ?case 
      by blast       
  }
  ultimately show ?case using Until_mltl 
    by (metis antisym_conv2 complen_geq_1 intervals_welldef.simps(9))
next
  case (Release_mltl \<phi>1 a b \<phi>2)
  {assume *: "complen_mltl \<phi>1 = 1 \<and> complen_mltl \<phi>2 = 1"
    {assume **: "b = 0"
      then have "b + max (complen_mltl \<phi>1 - 1) (complen_mltl \<phi>2) = 1"
        using * by auto
      then have ?case
        unfolding complen_mltl.simps  formula_progression_len1.simps
        by auto
    } moreover {assume **: "b > 0"
      {assume ***:  "0 < a \<and> a \<le> b"
        then have "complen_mltl
          (Until_mltl (Not_mltl \<phi>1) (a - 1) (b - 1) (Not_mltl \<phi>2))
          \<le> b + max (complen_mltl \<phi>1 - 1) (complen_mltl \<phi>2) - 1"
          using * unfolding complen_mltl.simps  formula_progression_len1.simps
          by auto
        then have ?case
        using *** by auto
    } moreover {assume ***: "0 = a \<and> a < b"
      have complen_1:"(complen_mltl (formula_progression_len1 \<phi>2 k)) = 1 \<and> (complen_mltl (formula_progression_len1 \<phi>1 k)) = 1"
        using * Release_mltl(3) unfolding intervals_welldef.simps
        using complen_one_implies_one_base by blast
       have "max 1 (max 1 (b - 1 + max (complen_mltl \<phi>1 - 1) (complen_mltl \<phi>2)))
            \<le> b + max (complen_mltl \<phi>1 - 1) (complen_mltl \<phi>2) - 1"
          using *** unfolding complen_mltl.simps  using * 
          by auto
        then have "complen_mltl
       (Or_mltl (Not_mltl (formula_progression_len1 \<phi>2 k))
                   (And_mltl
                     (Not_mltl (formula_progression_len1 \<phi>1 k))
                     (Until_mltl (Not_mltl \<phi>1) 0 (b - 1) (Not_mltl \<phi>2))))
      \<le> b + max (complen_mltl \<phi>1 - 1) (complen_mltl \<phi>2) - 1"
          unfolding complen_mltl.simps  using * complen_1
          by auto
        then have ?case
          using *** * 
          unfolding complen_mltl.simps  formula_progression_len1.simps
          by auto
      }
    ultimately have ?case
        unfolding complen_mltl.simps  formula_progression_len1.simps
        using ** 
        using Release_mltl.prems intervals_welldef.simps(10) zero_less_iff_neq_zero by blast
    }
    ultimately have ?case
      by blast
  } moreover {assume *: "complen_mltl \<phi>1 = 1 \<and> complen_mltl \<phi>2 > 1 \<and> complen_mltl (formula_progression_len1 \<phi>2 k) \<le> complen_mltl \<phi>2 - 1"
    {assume **: "b = 0"
      then have "complen_mltl
     (Not_mltl (formula_progression_len1 \<phi>2 k))
    \<le> b + max (complen_mltl \<phi>1 - 1) (complen_mltl \<phi>2) - 1"
        unfolding complen_mltl.simps 
        using * by auto
      then have ?case
        using ** unfolding complen_mltl.simps  formula_progression_len1.simps
        using * by auto
    } moreover {assume **: "b > 0"
      {assume ***: "0 < a \<and> a \<le> b"
        then have "complen_mltl
     (Until_mltl (Not_mltl \<phi>1) (a - 1) (b - 1) (Not_mltl \<phi>2))
    \<le> b + max (complen_mltl \<phi>1 - 1) (complen_mltl \<phi>2) - 1"
          unfolding complen_mltl.simps 
          using * ** by simp
      } moreover {assume ***: "0 = a \<and> a < b"
        have complen_1: "(complen_mltl (formula_progression_len1 \<phi>1 k)) = 1"
          using complen_one_implies_one_base Release_mltl(3)
          unfolding intervals_welldef.simps
          using * by auto
        have "max (complen_mltl (formula_progression_len1 \<phi>2 k))
           (max 1 (b - 1 + (complen_mltl \<phi>2)))
          \<le> b + (complen_mltl \<phi>2) - 1"
          using * **
          by fastforce 
        then have "max (complen_mltl (formula_progression_len1 \<phi>2 k))
           (max (complen_mltl (formula_progression_len1 \<phi>1 k))
             (b - 1 + max 0 (complen_mltl \<phi>2)))
          \<le> b + max 0 (complen_mltl \<phi>2) - 1"
          using * complen_1
          by auto
        then have "complen_mltl
             (Or_mltl (Not_mltl (formula_progression_len1 \<phi>2 k))
                         (And_mltl
                           (Not_mltl (formula_progression_len1 \<phi>1 k))
                           (Until_mltl (Not_mltl \<phi>1) 0
                             (b - 1) (Not_mltl \<phi>2))))
            \<le> b + max 0 (complen_mltl \<phi>2) - 1"
          using * 
        unfolding complen_mltl.simps formula_progression_len1.simps
          by auto
        then have "complen_mltl
             (Or_mltl (Not_mltl (formula_progression_len1 \<phi>2 k))
                         (And_mltl
                           (Not_mltl (formula_progression_len1 \<phi>1 k))
                           (Until_mltl (Not_mltl \<phi>1) 0
                             (b - 1) (Not_mltl \<phi>2))))
            \<le> b + max (complen_mltl \<phi>1 - 1) (complen_mltl \<phi>2) - 1"
          using * by auto
      }
      ultimately have ?case
        unfolding formula_progression_len1.simps
        using * ** by auto 
      }
    ultimately have ?case
      by blast
  } 
  moreover {assume *: "complen_mltl \<phi>2 = 1 \<and> complen_mltl \<phi>1 > 1 \<and> complen_mltl (formula_progression_len1 \<phi>1 k) \<le> complen_mltl \<phi>1 - 1"
      then have complen_fp_phi2: "complen_mltl (formula_progression_len1 \<phi>2 k) = 1"
        using complen_one_implies_one_base [of \<phi>2]
        Release_mltl(3) unfolding intervals_welldef.simps
        by blast
    {assume **: "b = 0"
      then have "b + max (complen_mltl \<phi>1 - 1) (complen_mltl \<phi>2) = 1 \<or> 
        complen_mltl (formula_progression_len1 \<phi>2 k)
        \<le> b + max (complen_mltl \<phi>1 - 1) (complen_mltl \<phi>2) - 1"
        using *  complen_fp_phi2
        by auto
      then have "b + max (complen_mltl \<phi>1 - 1) (complen_mltl \<phi>2) = 1 \<or>  complen_mltl
     (Not_mltl (formula_progression_len1 \<phi>2 k))
    \<le> b + max (complen_mltl \<phi>1 - 1) (complen_mltl \<phi>2) - 1"
        unfolding complen_mltl.simps  formula_progression_len1.simps
        by blast
      then have ?case using **
        by auto
    } 
    moreover {assume **: "b > 0"
      {assume ***:  "0 < a \<and> a \<le> b"
        have "b + max (complen_mltl \<phi>1 - 1) (complen_mltl \<phi>2) = 1 \<or>
          complen_mltl
           (Until_mltl (Not_mltl \<phi>1) (a - 1) (b - 1) (Not_mltl \<phi>2))
          \<le> b + max (complen_mltl \<phi>1 - 1) (complen_mltl \<phi>2) - 1"
          unfolding complen_mltl.simps using **
          by auto
        then have ?case
          using *** unfolding complen_mltl.simps formula_progression_len1.simps 
          by auto
      } moreover {assume ***: "0 = a \<and> a < b"
        have max_simp: "max (complen_mltl \<phi>1 - 1) 1 = (complen_mltl \<phi>1 - 1)"
          using * by auto
        have max_is: "max 1 (max (complen_mltl \<phi>1 - 1) (b - 1 + complen_mltl \<phi>1 - 1)) = 
          max (complen_mltl \<phi>1 - 1) (b - 1 + complen_mltl \<phi>1 - 1)"
          using * by auto
        have  "max (complen_mltl \<phi>1 - 1) (b - 1 + complen_mltl \<phi>1 - 1)
          \<le> b + (complen_mltl \<phi>1 - 1) - 1"
          using * ** by auto
        then have "max 1 (max (complen_mltl (formula_progression_len1 \<phi>1 k))
             (b - 1 + complen_mltl \<phi>1 - 1))
          \<le> b + (complen_mltl \<phi>1 - 1) - 1"
          using max_is ** * by auto
        then have "max 1 (max (complen_mltl (formula_progression_len1 \<phi>1 k))
               (b - 1 + max (complen_mltl \<phi>1 - 1) 1))
            \<le> b + max (complen_mltl \<phi>1 - 1) 1 - 1"
          using max_simp 
          by auto
        have "max (complen_mltl (formula_progression_len1 \<phi>2 k))
           (max (complen_mltl (formula_progression_len1 \<phi>1 k))
             (b - 1 + max (complen_mltl \<phi>1 - 1) (complen_mltl \<phi>2)))
          \<le> b + max (complen_mltl \<phi>1 - 1) (complen_mltl \<phi>2) - 1"
          using * ** complen_fp_phi2
          by auto
        then have "complen_mltl
           (Or_mltl (Not_mltl (formula_progression_len1 \<phi>2 k))
                       (And_mltl (Not_mltl (formula_progression_len1 \<phi>1 k))
                         (Until_mltl (Not_mltl \<phi>1) 0 (b - 1) (Not_mltl \<phi>2))))
          \<le> b + max (complen_mltl \<phi>1 - 1) (complen_mltl \<phi>2) - 1"
          unfolding complen_mltl.simps 
          by auto
        then have ?case
          using *** unfolding complen_mltl.simps formula_progression_len1.simps 
          by auto
      } 
      ultimately have ?case 
        using * ** 
        using Release_mltl.prems intervals_welldef.simps(9) zero_less_iff_neq_zero 
        by fastforce
    } 
    ultimately have ?case
      by blast  
  } moreover {assume *: "complen_mltl \<phi>1 > 1 \<and> complen_mltl \<phi>2 > 1 \<and> complen_mltl (formula_progression_len1 \<phi>1 k) \<le> complen_mltl \<phi>1 - 1 \<and> complen_mltl (formula_progression_len1 \<phi>2 k) \<le> complen_mltl \<phi>2 - 1"
    {assume **: "b = 0"
      then have "complen_mltl (Not_mltl (formula_progression_len1 \<phi>2 k))
    \<le> b + max (complen_mltl \<phi>1 - 1) (complen_mltl \<phi>2) - 1"
        unfolding complen_mltl.simps  formula_progression_len1.simps
        using * by auto
      then have ?case unfolding complen_mltl.simps  formula_progression_len1.simps
        using * **
        by auto
    } moreover {assume **: "b > 0"  
      {assume ***:  "0 < a \<and> a \<le> b"
        then have complen: "complen_mltl (Until_mltl (Not_mltl \<phi>1) (a - 1) (b - 1) (Not_mltl \<phi>2))
          \<le> b + max (complen_mltl \<phi>1 - 1) (complen_mltl \<phi>2) - 1"
          using * ** unfolding complen_mltl.simps 
          by simp
        have ?case
          unfolding complen_mltl.simps formula_progression_len1.simps
          using *** complen 
          by auto
      } moreover {assume ***: "0 = a \<and> a < b"
        have max_is: "max (complen_mltl \<phi>1 - 1) (b - 1 + max (complen_mltl \<phi>1 - 1) (complen_mltl \<phi>2))
      = (b - 1 + max (complen_mltl \<phi>1 - 1) (complen_mltl \<phi>2))"
          using **
          by simp
        have "max (complen_mltl \<phi>2 - 1) (b - 1 + max (complen_mltl \<phi>1 - 1) (complen_mltl \<phi>2))
          \<le> b + max (complen_mltl \<phi>1 - 1) (complen_mltl \<phi>2) - 1"
          using *** by auto
        then have "max (complen_mltl \<phi>2 - 1)
     (max (complen_mltl \<phi>1 - 1)
       (b - 1 + max (complen_mltl \<phi>1 - 1) (complen_mltl \<phi>2)))
    \<le> b + max (complen_mltl \<phi>1 - 1) (complen_mltl \<phi>2) - 1"
          using max_is
          by auto
        then have "max (complen_mltl (formula_progression_len1 \<phi>2 k))
     (max (complen_mltl (formula_progression_len1 \<phi>1 k))
       (b - 1 + max (complen_mltl \<phi>1 - 1) (complen_mltl \<phi>2)))
    \<le> b + max (complen_mltl \<phi>1 - 1) (complen_mltl \<phi>2) - 1"
          using * 
          by (smt (verit, best) max.absorb2 max.bounded_iff)
        then have "complen_mltl (Or_mltl (Not_mltl (formula_progression_len1 \<phi>2 k))
                 (And_mltl (Not_mltl (formula_progression_len1 \<phi>1 k))
                   (Until_mltl (Not_mltl \<phi>1) 0 (b - 1) (Not_mltl \<phi>2))))
          \<le> b + max (complen_mltl \<phi>1 - 1) (complen_mltl \<phi>2) - 1"
          using * ** unfolding complen_mltl.simps 
          by auto
        then have ?case
         unfolding formula_progression_len1.simps complen_mltl.simps 
         using ***
         by auto
      } 
      ultimately have ?case
        using *
        using "**" Release_mltl.prems intervals_welldef.simps(9) zero_less_iff_neq_zero
        by simp
    }
    ultimately have ?case 
      by blast       
  }
  ultimately show ?case using Release_mltl
    using complen_geq_1[of \<phi>1] complen_geq_1[of \<phi>2]
    by (metis antisym_conv2 intervals_welldef.simps(10))
qed

text \<open> Key helper lemma --- relates computation length and formula progression.
   Intuitively, the formula progression usually decreases the computation length. \<close>
lemma formula_progression_decreases_complen:
  assumes "intervals_welldef \<phi>"
  shows "complen_mltl \<phi> = 1 \<or> complen_mltl (formula_progression \<phi> \<pi>) = 1 \<or> complen_mltl (formula_progression \<phi> \<pi>) \<le> complen_mltl \<phi> - (length \<pi>)"
  using assms
proof (induct "length \<pi>" arbitrary: \<pi> \<phi>)
  case 0
  then show ?case by simp
next
  case (Suc x)
  {assume *: "Suc x = 1"
    then have ?case 
      using formula_progression_decreases_complen_base
      Suc by auto
  } moreover {assume *: "Suc x > 1"
    then have fp_is: "formula_progression \<phi> \<pi> =
    formula_progression (formula_progression_len1 \<phi> (\<pi> ! 0))
                (drop 1 \<pi>)"
      using Suc(2) formula_progression.simps[of \<phi> \<pi>] 
      by auto
    have eo_base: "complen_mltl \<phi> = 1 \<or>
    complen_mltl (formula_progression_len1 \<phi> (\<pi> ! 0))
    \<le> complen_mltl \<phi> - 1"
      using  formula_progression_decreases_complen_base[of \<phi> "\<pi> ! 0"]
      Suc(3) formula_progression_well_definedness_preserved_len1
      by blast
    {assume **: "complen_mltl \<phi> = 1"
      then have ?case
        by auto
    } moreover {assume **: "complen_mltl (formula_progression_len1 \<phi> (\<pi> ! 0))
    \<le> complen_mltl \<phi> - 1"
      {assume *** : "complen_mltl (formula_progression_len1 \<phi> (\<pi> ! 0)) = 1 "
        then have "complen_mltl (formula_progression (formula_progression_len1 \<phi> (\<pi> ! 0))
                (drop 1 \<pi>)) = 1"
  using complen_one_implies_one[of "formula_progression_len1 \<phi> (\<pi> ! 0)"] formula_progression_well_definedness_preserved_len1[OF Suc(3), of "\<pi> ! 0"]
  by blast
        then have "complen_mltl (formula_progression \<phi> \<pi>) = 1"
          using Suc *  formula_progression.simps
          by auto
        then have ?case
          by auto
      } moreover {assume ***: "complen_mltl
     (formula_progression (formula_progression_len1 \<phi> (\<pi> ! 0))
       (drop 1 \<pi>)) =
    1"
        then have "complen_mltl (formula_progression \<phi> \<pi>) = 1"
          using Suc *  formula_progression.simps
          by auto
        then have ?case
          by auto
      }
      moreover {assume **: "complen_mltl (formula_progression (formula_progression_len1 \<phi> (\<pi> ! 0))
                (drop 1 \<pi>)) \<le> complen_mltl \<phi> - length \<pi>"
        then have "complen_mltl (formula_progression (formula_progression_len1 \<phi> (\<pi> ! 0))
                (drop 1 \<pi>)) \<le> complen_mltl \<phi> - length \<pi>"
          by blast
        then have ?case
          by auto
      }
      ultimately have ?case
        using Suc(1)[of "drop 1 \<pi>" "formula_progression_len1 \<phi> (\<pi> ! 0)"]
        formula_progression_well_definedness_preserved_len1[OF Suc(3), of "\<pi> ! 0"]
        by (smt (verit) "**" Suc.hyps(2) diff_Suc_1 diff_Suc_eq_diff_pred diff_le_mono le_trans length_drop)   }
    ultimately have ?case
      using eo_base fp_is 
      by metis
  }
  ultimately show ?case by linarith
qed

paragraph \<open>Base case\<close>

lemma formula_progression_correctness_len1_helper:
  fixes \<phi>::"'a mltl"
  assumes "length \<pi> = 1"
  assumes "intervals_welldef \<phi>"
  assumes "length \<pi> \<ge> complen_mltl \<phi>"
  shows "(semantic_equiv (formula_progression_len1 \<phi> (\<pi> ! 0)) True_mltl) \<longleftrightarrow> semantics_mltl [\<pi>!0] \<phi>"
  using assms
proof -
  show ?thesis using assms
      proof (induction \<phi>)
        case True_mltl
        then show ?case  
          by (simp add: semantic_equiv_def)
      next
        case False_mltl
        then show ?case  by (simp add: semantic_equiv_def)
      next
        case (Prop_mltl x)
        then show ?case
          by (simp add: semantic_equiv_def)
      next
        case (Not_mltl \<phi>)
        then have "semantic_equiv (formula_progression_len1 \<phi> (\<pi> ! 0)) True_mltl =
          semantics_mltl [\<pi> ! 0] \<phi>"
          by simp
        then have "(\<forall>\<xi>. semantics_mltl \<xi> (formula_progression_len1 \<phi> (\<pi> ! 0)) =
         True) = semantics_mltl [\<pi> ! 0] \<phi>"
          unfolding semantic_equiv_def 
          by (meson semantics_mltl.simps(1))
        then show ?case unfolding semantics_mltl.simps formula_progression_len1.simps 
          unfolding semantic_equiv_def 
          using complen_bounded_by_1 
          using Not_mltl.prems(2) Not_mltl.prems(3) assms(1) by auto
      next
        case (And_mltl \<phi>1 \<phi>2)
        then show ?case 
          using formula_progression_len1.simps(5) semantic_equiv_def semantics_mltl.simps(1) semantics_mltl.simps(5)
         intervals_welldef.simps(5) complen_bounded_by_1
          by (smt (verit, best) complen_geq_1 complen_mltl.simps(5) dual_order.eq_iff max_def)
      next
        case (Or_mltl \<phi>1 \<phi>2)
        then have ind1: " semantic_equiv (formula_progression_len1 \<phi>1 (\<pi> ! 0)) True_mltl = semantics_mltl [\<pi> ! 0] \<phi>1"
          by simp
        have ind2: " semantic_equiv (formula_progression_len1 \<phi>2 (\<pi> ! 0)) True_mltl = semantics_mltl [\<pi> ! 0] \<phi>2"
          using Or_mltl
          by simp
         show ?case
            using complen_bounded_by_1 ind2 ind1
            by (smt (verit, ccfv_SIG) Or_mltl.prems(2) Or_mltl.prems(3) assms(1) complen_mltl.simps(6) formula_progression_len1.simps(6) intervals_welldef.simps(6) max.bounded_iff semantic_equiv_def semantics_mltl.simps(1) semantics_mltl.simps(6))
      next
        case (Future_mltl a b \<phi>)
        then show ?case 
          by (smt (verit, del_insts) Cons_nth_drop_Suc add.commute add_diff_cancel_right' complen_geq_one complen_mltl.simps(8) drop0 formula_progression_len1.simps(10) intervals_welldef.simps(7) leD le_add2 le_imp_less_Suc le_zero_eq list.size(4) nle_le plus_1_eq_Suc semantics_mltl.simps(7))
      next
        case (Global_mltl a b \<phi>)
        then show ?case using One_nat_def add_diff_cancel_left' add_diff_cancel_right' complen_geq_one complen_mltl.simps(7) drop0 formula_progression_len1.simps(10) formula_progression_len1.simps(4) formula_progression_len1.simps(9) impossible_Cons intervals_welldef.simps(8) le_add2 le_zero_eq less_numeral_extra(3) nle_le plus_1_eq_Suc semantic_equiv_def semantics_mltl.simps(4) semantics_mltl.simps(8)
          by (smt (verit))        
        (* May take a second to load *)
      next
        case (Until_mltl \<phi>1 a b \<phi>2)
        have "max (complen_mltl \<phi>1 - 1) (complen_mltl \<phi>2) \<ge> 1"
          using complen_geq_1 
          using max.coboundedI2 by blast
        then have "a = 0 \<and> b = 0"
          using Until_mltl(4) complen_geq_1 unfolding complen_mltl.simps
          by (metis Until_mltl.prems(3) add_diff_cancel_right' assms(1) bot_nat_0.extremum complen_mltl.simps(10) diff_is_0_eq' intervals_welldef.simps(9) le_antisym)        
        then show ?case
          using complen_bounded_by_1
          using Until_mltl.IH(2) Until_mltl.prems(2) Until_mltl.prems(3) assms(1) by force 
      next
        case (Release_mltl \<phi>1 a b \<phi>2)
        have ind2: " semantic_equiv (formula_progression_len1 \<phi>2 (\<pi> ! 0)) True_mltl = semantics_mltl [\<pi> ! 0] \<phi>2"
          using Release_mltl
          by simp
        have "max (complen_mltl \<phi>1 - 1) (complen_mltl \<phi>2) \<ge> 1"
          using complen_geq_1 
          using max.coboundedI2 by blast
        then have "a = 0 \<and> b = 0"
          using Release_mltl(4) complen_geq_1 unfolding complen_mltl.simps
          by (metis Release_mltl.prems(3) add_diff_cancel_right' assms(1) bot_nat_0.extremum complen_mltl.simps(9) diff_is_0_eq' intervals_welldef.simps(10) le_antisym)
        then have "formula_progression_len1 (Release_mltl \<phi>1 a b \<phi>2) (\<pi> ! 0) = Not_mltl ( Not_mltl (formula_progression_len1 \<phi>2 (\<pi> ! 0)))"
          unfolding formula_progression_len1.simps by auto 
        then show ?case using complen_bounded_by_1 ind2
          by (smt (verit, ccfv_threshold) One_nat_def \<open>a = 0 \<and> b = 0\<close> add.commute diff_diff_cancel diff_is_0_eq' drop0 le_numeral_extra(3) list.size(3) list.size(4) not_not_equiv not_one_le_zero plus_1_eq_Suc semantic_equiv_def semantics_mltl.simps(10))
      qed
    qed

lemma formula_progression_correctness_len1:
  fixes \<phi>::"'a mltl"
  assumes "length \<pi> = 1"
  assumes "intervals_welldef \<phi>"
  assumes "length \<pi> \<ge> complen_mltl \<phi>"
  shows "(formula_progression \<phi> \<pi> \<equiv>\<^sub>m True\<^sub>m) \<longleftrightarrow> \<pi> \<Turnstile>\<^sub>m \<phi>"
  using assms formula_progression_correctness_len1_helper
  by (metis Cons_nth_drop_Suc One_nat_def drop0 drop_eq_Nil2 formula_progression.simps le_numeral_extra(4) zero_less_one zero_neq_one)

paragraph \<open>Top-Level Result and Corollary\<close>

theorem formula_progression_correctness:
  fixes \<phi>::"'a mltl"
  assumes "intervals_welldef \<phi>"
  assumes "length \<pi> \<ge> complen_mltl \<phi>"
  shows "(formula_progression \<phi> \<pi> \<equiv>\<^sub>m True\<^sub>m) \<longleftrightarrow> \<pi> \<Turnstile>\<^sub>m \<phi>"
proof -
  have len_pi_geq1: "length \<pi> \<ge> 1"
    using assms complen_geq_1[of \<phi>] 
    by simp 
  {assume *: "length \<pi> = 1"
    then have ?thesis
      using formula_progression_correctness_len1 assms by blast
  } moreover {assume *: "length \<pi> > 1"
    let ?k = "length \<pi> - 1"
    have t1: "semantics_mltl (drop ?k \<pi>) (formula_progression \<phi> (take ?k \<pi> ))
    \<longleftrightarrow> semantics_mltl \<pi> \<phi>"
      using satisfiability_preservation assms * len_pi_geq1
      by (metis One_nat_def Suc_leI Suc_le_mono Suc_pred diff_less less_numeral_extra(1) order_less_le_trans)
    have len_1_tr: "length (drop ?k \<pi>) = 1"
      using len_pi_geq1 by fastforce

    have len_1: "length (drop (length \<pi> - 1) \<pi>) = 1"
      using len_1_tr by blast
    {assume * : "complen_mltl \<phi> = 1"
      then have "complen_mltl (formula_progression \<phi> (take (length \<pi> - 1) \<pi>))
    \<le> 1" using assms complen_one_implies_one[of \<phi> "take (length \<pi> - 1) \<pi>"] 
        by simp
    } moreover {assume *: "complen_mltl (formula_progression \<phi> (take (length \<pi> - 1) \<pi>))
    \<le> complen_mltl \<phi> - length (take (length \<pi> - 1) \<pi>)"
      then have "complen_mltl (formula_progression \<phi> (take (length \<pi> - 1) \<pi>))
    \<le> 1"
        using assms len_pi_geq1 by simp
    } moreover {assume *: "complen_mltl (formula_progression \<phi> (take (length \<pi> - 1) \<pi>)) = 1"
      then have "complen_mltl (formula_progression \<phi> (take (length \<pi> - 1) \<pi>))
        \<le> 1"
        by simp
    }
    ultimately have "complen_mltl (formula_progression \<phi> (take (length \<pi> - 1) \<pi>))
    \<le> 1"
      using assms formula_progression_decreases_complen[of \<phi> "(take (length \<pi> - 1) \<pi>)"]
      by blast
    (* This required proving that the computation length decreases as you progress through the formula *)
    then have "complen_mltl (formula_progression \<phi> (take (length \<pi> - 1) \<pi>))
    \<le> length (drop (length \<pi> - 1) \<pi>)"
      using len_1
      by auto
    then have t2: "(semantic_equiv (formula_progression (formula_progression \<phi> (take ?k \<pi>)) (drop ?k \<pi>))
     True_mltl) = semantics_mltl (drop ?k \<pi>) (formula_progression \<phi> (take ?k \<pi>))"
            using formula_progression_correctness_len1[of "drop ?k \<pi>" "(formula_progression \<phi> (take ?k \<pi> ))"]
                assms using len_1_tr
            using formula_progression_well_definedness_preserved 
            by blast
    have t3: "formula_progression (formula_progression \<phi> (take ?k \<pi>)) (drop ?k \<pi>)
    = formula_progression \<phi> \<pi> "
      using formula_progression_decomposition assms
      by (metis "*" One_nat_def Suc_leI diff_le_self zero_less_diff)
    have "length (take ?k \<pi>) > 0"
      using *
      by simp 
    then have ?thesis
      using t1 t2 t3 by argo 
  }
  ultimately show ?thesis
    using assms len_pi_geq1
    by linarith
qed

text \<open>Adds the crucial assumption that the length of the trace 
  is greater than or equal to the computation length of the formula.\<close>
corollary formula_progression_append:
  fixes \<phi>::"'a mltl"
  assumes "intervals_welldef \<phi>"
  assumes "\<pi> \<Turnstile>\<^sub>m \<phi>"
  assumes "length \<pi> \<ge> complen_mltl \<phi>"
  shows "(\<pi> @ \<zeta>) \<Turnstile>\<^sub>m \<phi>"
proof - 
  have len_geq1: "length \<pi> \<ge> 1"
    using assms(3) complen_geq_1 [of \<phi>]
    by auto
  have h1: "semantic_equiv (formula_progression \<phi> \<pi>) True_mltl"
      using len_geq1 formula_progression_correctness assms
      by blast
  have take_length:  "\<pi> = (take (length \<pi>) (\<pi> @ \<zeta> ))"
    by simp
  have drop_length: "\<zeta> = (drop (length \<pi>) (\<pi> @ \<zeta> ))"
    by simp
  have "semantics_mltl ( \<zeta>) True_mltl"
    using semantics_mltl.simps(1) by auto
  then show ?thesis 
    using len_geq1 h1 satisfiability_preservation[of "length \<pi>"]
    take_length drop_length assms linorder_le_less_linear take_all
    by (smt (verit, del_insts) semantic_equiv_def)
qed


paragraph \<open>Converse of Corollary and Combined Statement\<close>


text \<open>Alternate statement of the formula progression correctness lemma
that asserts formula progression on a trace of length one is 
semantically equivalent to False mltl when the formula is not satisfied\<close>
lemma formula_progression_correctness_len1_helper_alt:
  fixes \<phi>::"'a mltl"
  assumes "length \<pi> = 1"
  assumes "intervals_welldef \<phi>"
  assumes "length \<pi> \<ge> complen_mltl \<phi>"
  shows "((formula_progression_len1 \<phi> (\<pi> ! 0)) \<equiv>\<^sub>m False\<^sub>m) \<longleftrightarrow> \<not> ([\<pi>!0] \<Turnstile>\<^sub>m \<phi>)"
  using assms
proof -
  show ?thesis using assms
      proof (induction \<phi>)
        case True_mltl
        then show ?case  
          by (simp add: semantic_equiv_def)
      next
        case False_mltl
        then show ?case  by (simp add: semantic_equiv_def)
      next
        case (Prop_mltl x)
        then show ?case
          by (simp add: semantic_equiv_def)
      next
        case (Not_mltl \<phi>)
        then have "semantic_equiv (formula_progression_len1 \<phi> (\<pi> ! 0)) False_mltl =
          (\<not> semantics_mltl [\<pi> ! 0] \<phi>)"
          by simp
        then have "(\<forall>\<xi>. semantics_mltl \<xi> (formula_progression_len1 \<phi> (\<pi> ! 0)) =
         False) = (\<not> semantics_mltl [\<pi> ! 0] \<phi>)"
          unfolding semantic_equiv_def
          by (meson semantics_mltl.simps(2))  
        then show ?case unfolding semantics_mltl.simps formula_progression_len1.simps 
          unfolding semantic_equiv_def 
          using complen_bounded_by_1 
          using Not_mltl.prems(2) Not_mltl.prems(3) assms(1) by auto
      next
        case (And_mltl \<phi>1 \<phi>2)
        then show ?case 
          using formula_progression_len1.simps(5) semantic_equiv_def semantics_mltl.simps(1) semantics_mltl.simps(5)
         intervals_welldef.simps(5) complen_bounded_by_1
          by (smt (verit, ccfv_threshold) formula_progression_correctness_len1_helper semantics_mltl.simps(2))
      next
        case (Or_mltl \<phi>1 \<phi>2)
        then have ind1: "semantic_equiv (formula_progression_len1 \<phi>1 (\<pi> ! 0)) False_mltl = (\<not> semantics_mltl [\<pi> ! 0] \<phi>1)"
          by simp
        have ind2: "semantic_equiv (formula_progression_len1 \<phi>2 (\<pi> ! 0)) False_mltl = (\<not> semantics_mltl [\<pi> ! 0] \<phi>2)"
          using Or_mltl
          by simp
         show ?case
            using complen_bounded_by_1 ind2 ind1
            by (smt (verit) formula_progression_len1.simps(6) semantic_equiv_def semantics_mltl.simps(2) semantics_mltl.simps(6)) 
      next
        case (Future_mltl a b \<phi>)
        then show ?case 
          by (smt (verit, del_insts) Cons_nth_drop_Suc add.commute add_diff_cancel_right' complen_geq_one complen_mltl.simps(8) drop0 formula_progression_len1.simps(10) intervals_welldef.simps(7) leD le_add2 le_imp_less_Suc le_zero_eq list.size(4) nle_le plus_1_eq_Suc semantics_mltl.simps(7))
      next
        case (Global_mltl a b \<phi>)
        then show ?case using One_nat_def add_diff_cancel_left' add_diff_cancel_right' complen_geq_one complen_mltl.simps(7) drop0 formula_progression_len1.simps(10) formula_progression_len1.simps(4) formula_progression_len1.simps(9) impossible_Cons intervals_welldef.simps(8) le_add2 le_zero_eq less_numeral_extra(3) nle_le plus_1_eq_Suc semantic_equiv_def semantics_mltl.simps(4) semantics_mltl.simps(8)
          by (smt (verit))        
        (* May take a second to load *)
      next
        case (Until_mltl \<phi>1 a b \<phi>2)
        have "max (complen_mltl \<phi>1 - 1) (complen_mltl \<phi>2) \<ge> 1"
          using complen_geq_1 
          using max.coboundedI2 by blast
        then have "a = 0 \<and> b = 0"
          using Until_mltl(4) complen_geq_1 unfolding complen_mltl.simps
          by (metis Until_mltl.prems(3) add_diff_cancel_right' assms(1) bot_nat_0.extremum complen_mltl.simps(10) diff_is_0_eq' intervals_welldef.simps(9) le_antisym)        
        then show ?case
          using complen_bounded_by_1
          using Until_mltl.IH(2) Until_mltl.prems(2) Until_mltl.prems(3) assms(1) by force 
      next
        case (Release_mltl \<phi>1 a b \<phi>2)
        have ind2: " semantic_equiv (formula_progression_len1 \<phi>2 (\<pi> ! 0)) False_mltl = (\<not> semantics_mltl [\<pi> ! 0] \<phi>2)"
          using Release_mltl
          by simp
        have "max (complen_mltl \<phi>1 - 1) (complen_mltl \<phi>2) \<ge> 1"
          using complen_geq_1 
          using max.coboundedI2 by blast
        then have "a = 0 \<and> b = 0"
          using Release_mltl(4) complen_geq_1 unfolding complen_mltl.simps
          by (metis Release_mltl.prems(3) add_diff_cancel_right' assms(1) bot_nat_0.extremum complen_mltl.simps(9) diff_is_0_eq' intervals_welldef.simps(10) le_antisym)
        then have "formula_progression_len1 (Release_mltl \<phi>1 a b \<phi>2) (\<pi> ! 0) = Not_mltl ( Not_mltl (formula_progression_len1 \<phi>2 (\<pi> ! 0)))"
          unfolding formula_progression_len1.simps by auto 
        then show ?case using complen_bounded_by_1 ind2
          by (smt (verit, ccfv_threshold) One_nat_def \<open>a = 0 \<and> b = 0\<close> add.commute diff_diff_cancel diff_is_0_eq' drop0 le_numeral_extra(3) list.size(3) list.size(4) not_not_equiv not_one_le_zero plus_1_eq_Suc semantic_equiv_def semantics_mltl.simps(10))
      qed
    qed


text \<open>Alternate statement of the formula-progression-correctness lemma
with False in the case that the semantics are not satisfied.\<close>
lemma formula_progression_correctness_len1_alt:
  fixes \<phi>::"'a mltl"
  assumes "length \<pi> = 1"
  assumes "intervals_welldef \<phi>"
  assumes "length \<pi> \<ge> complen_mltl \<phi>"
  shows "((formula_progression \<phi> \<pi>) \<equiv>\<^sub>m False_mltl) \<longleftrightarrow> \<not> \<pi> \<Turnstile>\<^sub>m \<phi>"
  using assms formula_progression_correctness_len1_helper_alt
  by (metis Cons_nth_drop_Suc One_nat_def drop0 drop_eq_Nil2 formula_progression.simps le_numeral_extra(4) zero_less_one zero_neq_one)

theorem formula_progression_correctness_alt:
  fixes \<phi>::"'a mltl"
  assumes "intervals_welldef \<phi>"
  assumes "length \<pi> \<ge> complen_mltl \<phi>"
  shows "((formula_progression \<phi> \<pi>) \<equiv>\<^sub>m False_mltl) \<longleftrightarrow> \<not> (\<pi> \<Turnstile>\<^sub>m \<phi>)"
proof -
  have len_pi_geq1: "length \<pi> \<ge> 1"
    using assms complen_geq_1[of \<phi>] 
    by simp 
  {assume *: "length \<pi> = 1"
    then have ?thesis using assms 
      using formula_progression_correctness_len1_alt assms by blast
  } moreover {assume *: "length \<pi> > 1"
    let ?k = "length \<pi> - 1"
    have t1: "semantics_mltl (drop ?k \<pi>) (formula_progression \<phi> (take ?k \<pi> ))
    \<longleftrightarrow> semantics_mltl \<pi> \<phi>"
      using satisfiability_preservation assms * len_pi_geq1
      by (metis One_nat_def Suc_leI Suc_le_mono Suc_pred diff_less less_numeral_extra(1) order_less_le_trans)
    have len_1_tr: "length (drop ?k \<pi>) = 1"
      using len_pi_geq1 by fastforce

    have len_1: "length (drop (length \<pi> - 1) \<pi>) = 1"
      using len_1_tr by blast
    {assume * : "complen_mltl \<phi> = 1"
      then have "complen_mltl (formula_progression \<phi> (take (length \<pi> - 1) \<pi>))
    \<le> 1" using assms complen_one_implies_one[of \<phi> "take (length \<pi> - 1) \<pi>"] 
        by simp
    } moreover {assume *: "complen_mltl (formula_progression \<phi> (take (length \<pi> - 1) \<pi>))
    \<le> complen_mltl \<phi> - length (take (length \<pi> - 1) \<pi>)"
      then have "complen_mltl (formula_progression \<phi> (take (length \<pi> - 1) \<pi>))
    \<le> 1"
        using assms len_pi_geq1 by simp
    } moreover {assume *: "complen_mltl (formula_progression \<phi> (take (length \<pi> - 1) \<pi>)) = 1"
      then have "complen_mltl (formula_progression \<phi> (take (length \<pi> - 1) \<pi>))
        \<le> 1"
        by simp
    }
    ultimately have "complen_mltl (formula_progression \<phi> (take (length \<pi> - 1) \<pi>))
    \<le> 1"
      using assms formula_progression_decreases_complen[of \<phi> "(take (length \<pi> - 1) \<pi>)"]
      by blast
    (* This required proving that the computation length decreases as you progress through the formula *)
    then have "complen_mltl (formula_progression \<phi> (take (length \<pi> - 1) \<pi>))
    \<le> length (drop (length \<pi> - 1) \<pi>)"
      using len_1
      by auto
    then have t2: "(semantic_equiv (formula_progression (formula_progression \<phi> (take ?k \<pi>)) (drop ?k \<pi>))
     True_mltl) = semantics_mltl (drop ?k \<pi>) (formula_progression \<phi> (take ?k \<pi>))"
            using formula_progression_correctness_len1[of "drop ?k \<pi>" "(formula_progression \<phi> (take ?k \<pi> ))"]
                assms using len_1_tr
            using formula_progression_well_definedness_preserved 
            by blast
    have t3: "formula_progression (formula_progression \<phi> (take ?k \<pi>)) (drop ?k \<pi>)
    = formula_progression \<phi> \<pi> "
      using formula_progression_decomposition assms
      by (metis "*" One_nat_def Suc_leI diff_le_self zero_less_diff)
    have "length (take ?k \<pi>) > 0"
      using *
      by simp 
    then have ?thesis
      using t1 t2 t3
      by (metis \<open>complen_mltl (formula_progression \<phi> (take (length \<pi> - 1) \<pi>)) \<le> length (drop (length \<pi> - 1) \<pi>)\<close> assms(1) formula_progression_correctness_len1_alt formula_progression_well_definedness_preserved len_1_tr)
  }
  ultimately show ?thesis
    using assms len_pi_geq1
    by linarith
qed


lemma formula_progression_true_or_false:
  fixes \<phi>::"'a mltl"
  assumes "intervals_welldef \<phi>"
  assumes "length \<pi> \<ge> complen_mltl \<phi>"
  shows "((formula_progression \<phi> \<pi>) \<equiv>\<^sub>m False\<^sub>m) \<or> 
         ((formula_progression \<phi> \<pi>) \<equiv>\<^sub>m True\<^sub>m)"
  using formula_progression_correctness formula_progression_correctness_alt
  using assms by blast


text \<open>The inverse statement of formula-progression-append lemma\<close>
corollary formula_progression_append_converse:
  fixes \<phi>::"'a mltl"
  assumes "intervals_welldef \<phi>"
  assumes "\<not> \<pi> \<Turnstile>\<^sub>m \<phi>"
  assumes "length \<pi> \<ge> complen_mltl \<phi>"
  shows "\<not> (\<pi> @ \<zeta>) \<Turnstile>\<^sub>m \<phi>"
proof- 
  have len_geq1: "length \<pi> \<ge> 1"
    using assms(3) complen_geq_1 [of \<phi>]
    by auto
  have h1: "semantic_equiv (formula_progression \<phi> \<pi>) False_mltl"
    using len_geq1 formula_progression_correctness_alt assms by blast
  have take_length:  "\<pi> = (take (length \<pi>) (\<pi> @ \<zeta> ))"
      by simp
  have drop_length: "\<zeta> = (drop (length \<pi>) (\<pi> @ \<zeta> ))"
    by simp
  have "semantics_mltl ( \<zeta>) True_mltl"
    using semantics_mltl.simps(1) by auto
  then show ?thesis 
    using len_geq1 h1 satisfiability_preservation[of "length \<pi>"]
    take_length drop_length assms linorder_le_less_linear take_all
    by (smt (verit) semantic_equiv_def semantics_mltl.simps(2))
qed


text \<open>An important property of complen-mltl that says states in the trace
after the computation length does not affect the semantic 
satisfaction of the formula.\<close>
corollary complen_property:
  fixes \<phi>::"'a mltl"
  assumes "intervals_welldef \<phi>"
  assumes "length \<pi> \<ge> complen_mltl \<phi>"
  shows "\<pi> \<Turnstile>\<^sub>m \<phi> \<longleftrightarrow> (\<forall>\<zeta>. (\<pi> @ \<zeta>) \<Turnstile>\<^sub>m \<phi>)"
  using formula_progression_append 
  using formula_progression_append_converse assms by blast 


subsection "Formula Progression Examples"

(*the value of this simplifies to False_mltl*)
value "formula_progression 
       ((G\<^sub>m [0,2] (Prop_mltl 0))::nat mltl) 
       [{0::nat}, {0}, {1}]"

(*tr = [{0::nat}, {0}, {1}], length is 3*)
value "[{0::nat}, {0}, {1}] ! 0"
value "drop 1 ([{0::nat}, {0}, {1}])"
value "formula_progression_len1 ((G\<^sub>m [0,2] (Prop_mltl 0))::nat mltl) {0}"
(*the formula above simplifies to ((Global_mltl (Prop_mltl 0) 0 1)::nat mltl)*)
value "formula_progression 
       (formula_progression_len1 
           ((G\<^sub>m [0,2] (Prop_mltl 0))::nat mltl) 
           {0}
       ) 
       [{0}, {1}]"

value "formula_progression 
       ((G\<^sub>m [0,1] (Prop_mltl 0))::nat mltl) 
       [{0}, {1}]"
(*Still false*)
value "formula_progression 
       (formula_progression_len1 
           ((Global_mltl 0 1 (Prop_mltl 0))::nat mltl) 
           {0}) 
       [{1}]"

value "formula_progression_len1 ((G\<^sub>m [0,1] (Prop_mltl 0))::nat mltl) {0}"
(*this formula simplifies to G[0,0]p0*)


value "formula_progression 
       ((G\<^sub>m [0,0] (Prop_mltl 0))::nat mltl) 
       [{1}]"
(*Still false*)
value "formula_progression_len1 
       ((G\<^sub>m [0,0] (Prop_mltl 0))::nat mltl) 
       {1}"


subsection \<open>Code Export\<close>

export_code
formula_progression
in SML module_name FP

end