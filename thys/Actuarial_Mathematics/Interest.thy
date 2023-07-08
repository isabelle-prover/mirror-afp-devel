theory Interest
  imports Preliminaries
begin


section \<open>List of Actuarial Notations (Global Scope)\<close>

definition i_nom :: "real \<Rightarrow> nat \<Rightarrow> real" ("$i[_]^{_}" [0,0] 200)
  where "$i[i]^{m} \<equiv> m * ((1+i).^(1/m) - 1)"  \<comment> \<open>nominal interest rate\<close>
definition i_force :: "real \<Rightarrow> real" ("$\<delta>[_]" [0] 200)
  where "$\<delta>[i] \<equiv> ln (1+i)" \<comment> \<open>force of interest\<close>
definition d_nom :: "real \<Rightarrow> nat \<Rightarrow> real" ("$d[_]^{_}" [0,0] 200)
  where "$d[i]^{m} \<equiv> $i[i]^{m} / (1 + $i[i]^{m}/m)"  \<comment> \<open>discount rate\<close> 
abbreviation d_nom_yr :: "real \<Rightarrow> real" ("$d[_]" [0] 200)
  where "$d[i] \<equiv> $d[i]^{1}"  \<comment> \<open>Post-fix "yr" stands for "year".\<close>
definition v_pres :: "real \<Rightarrow> real" ("$v[_]" [0] 200)
  where "$v[i] \<equiv> 1 / (1+i)"  \<comment> \<open>present value factor\<close>
definition ann :: "real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" ("$a[_]^{_}'__" [0,0,101] 200)
  where "$a[i]^{m}_n \<equiv> \<Sum>k<n*m. $v[i].^((k+1::nat)/m) / m"
    \<comment> \<open>present value of an immediate annuity\<close>
abbreviation ann_yr :: "real \<Rightarrow> nat \<Rightarrow> real" ("$a[_]'__" [0,101] 200)
  where "$a[i]_n \<equiv> $a[i]^{1}_n"
definition acc :: "real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" ("$s[_]^{_}'__" [0,0,101] 200)
  where "$s[i]^{m}_n \<equiv> \<Sum>k<n*m. (1+i).^((k::nat)/m) / m"
    \<comment> \<open>future value of an immediate annuity\<close>
    \<comment> \<open>The name "acc" stands for "accumulation".\<close>
abbreviation acc_yr :: "real \<Rightarrow> nat \<Rightarrow> real" ("$s[_]'__" [0] 200)
  where "$s[i]_n \<equiv> $s[i]^{1}_n"
definition ann_due :: "real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" ("$a''''[_]^{_}'__" [0,0,101] 200)
  where "$a''[i]^{m}_n \<equiv> \<Sum>k<n*m. $v[i].^((k::nat)/m) / m"
    \<comment> \<open>present value of an annuity-due\<close>
abbreviation ann_due_yr :: "real \<Rightarrow> nat \<Rightarrow> real" ("$a''''[_]'__" [0,101] 200)
  where "$a''[i]_n \<equiv> $a''[i]^{1}_n"
definition acc_due :: "real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" ("$s''''[_]^{_}'__" [0,0,101] 200)
  where "$s''[i]^{m}_n \<equiv> \<Sum>k<n*m. (1+i).^((k+1::nat)/m) / m"
    \<comment> \<open>future value of an annuity-due\<close>
abbreviation acc_due_yr :: "real \<Rightarrow> nat \<Rightarrow> real" ("$s''''[_]'__" [0,101] 200)
  where "$s''[i]_n \<equiv> $s''[i]^{1}_n"
definition ann_cont :: "real \<Rightarrow> real \<Rightarrow> real" ("$a''[_]'__" [0,101] 200)
  where "$a'[i]_n \<equiv> integral {0..n} (\<lambda>t::real. $v[i].^t)"
    \<comment> \<open>present value of a continuous annuity\<close>
definition acc_cont :: "real \<Rightarrow> real \<Rightarrow> real" ("$s''[_]'__" [0,101] 200)
  where "$s'[i]_n \<equiv> integral {0..n} (\<lambda>t::real. (1+i).^t)"
    \<comment> \<open>future value of a continuous annuity\<close>
definition perp :: "real \<Rightarrow> nat \<Rightarrow> real" ("$a[_]^{_}'_\<infinity>" [0,0] 200)
  where "$a[i]^{m}_\<infinity> \<equiv> 1 / $i[i]^{m}"
    \<comment> \<open>present value of a perpetual annuity\<close>
abbreviation perp_yr :: "real \<Rightarrow> real" ("$a[_]'_\<infinity>" [0] 200)
  where "$a[i]_\<infinity> \<equiv> $a[i]^{1}_\<infinity>"
definition perp_due :: "real \<Rightarrow> nat \<Rightarrow> real" ("$a''''[_]^{_}'_\<infinity>" [0,0] 200)
  where "$a''[i]^{m}_\<infinity> \<equiv> 1 / $d[i]^{m}"
    \<comment> \<open>present value of a perpetual annuity-due\<close>
abbreviation perp_due_yr :: "real \<Rightarrow> real" ("$a''''[_]'_\<infinity>" [0] 200)
  where "$a''[i]_\<infinity> \<equiv> $a''[i]^{1}_\<infinity>"
definition ann_incr :: "nat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real"
  ("$'(I^{_}a')[_]^{_}'__" [0,0,0,101] 200)
  where "$(I^{l}a)[i]^{m}_n \<equiv> \<Sum>k<n*m. $v[i].^((k+1::nat)/m) * \<lceil>l*(k+1::nat)/m\<rceil> / (l*m)"
    \<comment> \<open>present value of an increasing annuity\<close>
    \<comment> \<open>This is my original definition.\<close>
    \<comment> \<open>Here, "l" represents the number of increments per unit time.\<close>
abbreviation ann_incr_lvl :: "real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real"
  ("$'(Ia')[_]^{_}'__" [0,0,101] 200)
  where "$(Ia)[i]^{m}_n \<equiv> $(I^{1}a)[i]^{m}_n"
    \<comment> \<open>The post-fix "lvl" stands for "level".\<close>
abbreviation ann_incr_yr :: "real \<Rightarrow> nat \<Rightarrow> real" ("$'(Ia')[_]'__" [0,101] 200)
  where "$(Ia)[i]_n \<equiv> $(Ia)[i]^{1}_n"
definition acc_incr :: "nat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real"
  ("$'(I^{_}s')[_]^{_}'__" [0,0,0,101] 200)
  where "$(I^{l}s)[i]^{m}_n \<equiv> \<Sum>k<n*m. (1+i).^(n-(k+1::nat)/m) * \<lceil>l*(k+1::nat)/m\<rceil> / (l*m)"
    \<comment> \<open>future value of an increasing annuity\<close>
abbreviation acc_incr_lvl :: "real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real"
  ("$'(Is')[_]^{_}'__" [0,0,101] 200)
  where "$(Is)[i]^{m}_n \<equiv> $(I^{1}s)[i]^{m}_n"
abbreviation acc_incr_yr :: "real \<Rightarrow> nat \<Rightarrow> real" ("$'(Is')[_]'__" [0,101] 200)
  where "$(Is)[i]_n \<equiv> $(Is)[i]^{1}_n"
definition ann_due_incr :: "nat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real"
  ("$'(I^{_}a''''')[_]^{_}'__" [0,0,0,101] 200)
  where "$(I^{l}a'')[i]^{m}_n \<equiv> \<Sum>k<n*m. $v[i].^((k::nat)/m) * \<lceil>l*(k+1::nat)/m\<rceil> / (l*m)"
abbreviation ann_due_incr_lvl :: "real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real"
  ("$'(Ia''''')[_]^{_}'__" [0,0,101] 200)
  where "$(Ia'')[i]^{m}_n \<equiv> $(I^{1}a'')[i]^{m}_n"
abbreviation ann_due_incr_yr :: "real \<Rightarrow> nat \<Rightarrow> real" ("$'(Ia''''')[_]'__" [0,101] 200)
  where "$(Ia'')[i]_n \<equiv> $(Ia'')[i]^{1}_n"
definition acc_due_incr :: "nat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real"
  ("$'(I^{_}s''''')[_]^{_}'__" [0,0,0,101] 200)
  where "$(I^{l}s'')[i]^{m}_n \<equiv> \<Sum>k<n*m. (1+i).^(n-(k::nat)/m) * \<lceil>l*(k+1::nat)/m\<rceil> / (l*m)"
abbreviation acc_due_incr_lvl :: "real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real"
  ("$'(Is''''')[_]^{_}'__" [0,0,101] 200)
  where "$(Is'')[i]^{m}_n \<equiv> $(I^{1}s'')[i]^{m}_n"
abbreviation acc_due_incr_yr :: "real \<Rightarrow> nat \<Rightarrow> real" ("$'(Is''''')[_]'__" [0,101] 200)
  where "$(Is'')[i]_n \<equiv> $(Is'')[i]^{1}_n"
definition perp_incr :: "nat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real" ("$'(I^{_}a')[_]^{_}'_\<infinity>" [0,0,0] 200)
  where "$(I^{l}a)[i]^{m}_\<infinity> \<equiv> lim (\<lambda>n. $(I^{l}a)[i]^{m}_n)"
abbreviation perp_incr_lvl :: "real \<Rightarrow> nat \<Rightarrow> real" ("$'(Ia')[_]^{_}'_\<infinity>" [0,0] 200)
  where "$(Ia)[i]^{m}_\<infinity> \<equiv> $(I^{1}a)[i]^{m}_\<infinity>"
abbreviation perp_incr_yr :: "real \<Rightarrow> real" ("$'(Ia')[_]'_\<infinity>" [0] 200)
  where "$(Ia)[i]_\<infinity> \<equiv> $(Ia)[i]^{1}_\<infinity>"
definition perp_due_incr :: "nat \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real" ("$'(I^{_}a''''')[_]^{_}'_\<infinity>" [0,0,0] 200)
  where "$(I^{l}a'')[i]^{m}_\<infinity> \<equiv> lim (\<lambda>n. $(I^{l}a'')[i]^{m}_n)"
abbreviation perp_due_incr_lvl :: "real \<Rightarrow> nat \<Rightarrow> real" ("$'(Ia''''')[_]^{_}'_\<infinity>" [0,0] 200)
  where "$(Ia'')[i]^{m}_\<infinity> \<equiv> $(I^{1}a'')[i]^{m}_\<infinity>"
abbreviation perp_due_incr_yr :: "real \<Rightarrow> real" ("$'(Ia''''')[_]'_\<infinity>" [0] 200)
  where "$(Ia'')[i]_\<infinity> \<equiv> $(Ia'')[i]^{1}_\<infinity>"


section \<open>Theory of Interest\<close>

locale interest =
  fixes i :: real  \<comment> \<open>i stands for an interest rate.\<close>
  assumes v_futr_pos: "1 + i > 0"  \<comment> \<open>Assume that the future value is positive.\<close>

context interest
begin

abbreviation i_nom' :: "nat \<Rightarrow> real" ("$i^{_}" [0] 200)
  where "$i^{m} \<equiv> $i[i]^{m}"
abbreviation i_force' :: real ("$\<delta>")
  where "$\<delta> \<equiv> $\<delta>[i]"
abbreviation d_nom' :: "nat \<Rightarrow> real" ("$d^{_}" [0] 200)
  where "$d^{m} \<equiv> $d[i]^{m}"
abbreviation d_nom_yr' :: real ("$d")
  where "$d \<equiv> $d[i]"
abbreviation v_pres' :: real ("$v")
  where "$v \<equiv> $v[i]"
abbreviation ann' :: "nat \<Rightarrow> nat \<Rightarrow> real" ("$a^{_}'__" [0,101] 200)
  where "$a^{m}_n \<equiv> $a[i]^{m}_n"
abbreviation ann_yr' :: "nat \<Rightarrow> real" ("$a'__" [101] 200)
  where "$a_n \<equiv> $a[i]_n"
abbreviation acc' :: "nat \<Rightarrow> nat \<Rightarrow> real" ("$s^{_}'__" [0,101] 200)
  where "$s^{m}_n \<equiv> $s[i]^{m}_n"
abbreviation acc_yr' :: "nat \<Rightarrow> real" ("$s'__" [101] 200)
  where "$s_n \<equiv> $s[i]_n"
abbreviation ann_due' :: "nat \<Rightarrow> nat \<Rightarrow> real" ("$a''''^{_}'__" [0,101] 200)
  where "$a''^{m}_n \<equiv> $a''[i]^{m}_n"
abbreviation ann_due_yr' :: "nat \<Rightarrow> real" ("$a'''''__" [101] 200)
  where "$a''_n \<equiv> $a''[i]_n"
abbreviation acc_due' :: "nat \<Rightarrow> nat \<Rightarrow> real" ("$s''''^{_}'__" [0,101] 200)
  where "$s''^{m}_n \<equiv> $s''[i]^{m}_n"
abbreviation acc_due_yr' :: "nat \<Rightarrow> real" ("$s'''''__" [101] 200)
  where "$s''_n \<equiv> $s''[i]_n"
abbreviation ann_cont' :: "real \<Rightarrow> real" ("$a'''__" [101] 200)
  where "$a'_n \<equiv> $a'[i]_n"
abbreviation acc_cont' :: "real \<Rightarrow> real" ("$s'''__" [101] 200)
  where "$s'_n \<equiv> $s'[i]_n"
abbreviation perp' :: "nat \<Rightarrow> real" ("$a^{_}'_\<infinity>" [0] 200)
  where "$a^{m}_\<infinity> \<equiv> $a[i]^{m}_\<infinity>"
abbreviation perp_yr' :: real ("$a'_\<infinity>")
  where "$a_\<infinity> \<equiv> $a[i]_\<infinity>"
abbreviation perp_due' :: "nat \<Rightarrow> real" ("$a''''^{_}'_\<infinity>" [0] 200)
  where "$a''^{m}_\<infinity> \<equiv> $a''[i]^{m}_\<infinity>"
abbreviation perp_due_yr' :: real ("$a'''''_\<infinity>")
  where "$a''_\<infinity> \<equiv> $a''[i]_\<infinity>"
abbreviation ann_incr' :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" ("$'(I^{_}a')^{_}'__" [0,0,101] 200)
  where "$(I^{l}a)^{m}_n \<equiv> $(I^{l}a)[i]^{m}_n"
abbreviation ann_incr_lvl' :: "nat \<Rightarrow> nat \<Rightarrow> real" ("$'(Ia')^{_}'__" [0,101] 200)
  where "$(Ia)^{m}_n \<equiv> $(Ia)[i]^{m}_n"
abbreviation ann_incr_yr' :: "nat \<Rightarrow> real" ("$'(Ia')'__" [101] 200)
  where "$(Ia)_n \<equiv> $(Ia)[i]_n"
abbreviation acc_incr' :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" ("$'(I^{_}s')^{_}'__" [0,0,101] 200)
  where "$(I^{l}s)^{m}_n \<equiv> $(I^{l}s)[i]^{m}_n"
abbreviation acc_incr_lvl' :: "nat \<Rightarrow> nat \<Rightarrow> real" ("$'(Is')^{_}'__" [0,101] 200)
  where "$(Is)^{m}_n \<equiv> $(Is)[i]^{m}_n"
abbreviation acc_incr_yr' :: "nat \<Rightarrow> real" ("$'(Is')'__" [101] 200)
  where "$(Is)_n \<equiv> $(Is)[i]_n"
abbreviation ann_due_incr' :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" ("$'(I^{_}a''''')^{_}'__" [0,0,101] 200)
  where "$(I^{l}a'')^{m}_n \<equiv> $(I^{l}a'')[i]^{m}_n"
abbreviation ann_due_incr_lvl' :: "nat \<Rightarrow> nat \<Rightarrow> real" ("$'(Ia''''')^{_}'__" [0,101] 200)
  where "$(Ia'')^{m}_n \<equiv> $(Ia'')[i]^{m}_n"
abbreviation ann_due_incr_yr' :: "nat \<Rightarrow> real" ("$'(Ia''''')'__" [101] 200)
  where "$(Ia'')_n \<equiv> $(Ia'')[i]_n"
abbreviation acc_due_incr' :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" ("$'(I^{_}s''''')^{_}'__" [0,0,101] 200)
  where "$(I^{l}s'')^{m}_n \<equiv> $(I^{l}s'')[i]^{m}_n"
abbreviation acc_due_incr_lvl' :: "nat \<Rightarrow> nat \<Rightarrow> real" ("$'(Is''''')^{_}'__" [0,101] 200)
  where "$(Is'')^{m}_n \<equiv> $(Is'')[i]^{m}_n"
abbreviation acc_due_incr_yr' :: "nat \<Rightarrow> real" ("$'(Is''''')'__" [101] 200)
  where "$(Is'')_n \<equiv> $(Is'')[i]_n"
abbreviation perp_incr' :: "nat \<Rightarrow> nat \<Rightarrow> real" ("$'(I^{_}a')^{_}'_\<infinity>" [0,0] 200)
  where "$(I^{l}a)^{m}_\<infinity> \<equiv> $(I^{l}a)[i]^{m}_\<infinity>"
abbreviation perp_incr_lvl' :: "nat \<Rightarrow> real" ("$'(Ia')^{_}'_\<infinity>" [0] 200)
  where "$(Ia)^{m}_\<infinity> \<equiv> $(Ia)[i]^{m}_\<infinity>"
abbreviation perp_incr_yr' :: real ("$'(Ia')'_\<infinity>")
  where "$(Ia)_\<infinity> \<equiv> $(Ia)[i]_\<infinity>"
abbreviation perp_due_incr' :: "nat \<Rightarrow> nat \<Rightarrow> real" ("$'(I^{_}a''''')^{_}'_\<infinity>" [0,0] 200)
  where "$(I^{l}a'')^{m}_\<infinity> \<equiv> $(I^{l}a'')[i]^{m}_\<infinity>"
abbreviation perp_due_incr_lvl' :: "nat \<Rightarrow> real" ("$'(Ia''''')^{_}'_\<infinity>" [0] 200)
  where "$(Ia'')^{m}_\<infinity> \<equiv> $(Ia'')[i]^{m}_\<infinity>"
abbreviation perp_due_incr_yr' :: real ("$'(Ia''''')'_\<infinity>")
  where "$(Ia'')_\<infinity> \<equiv> $(Ia'')[i]_\<infinity>"

lemma v_futr_m_pos: "1 + $i^{m}/m > 0" if "m \<noteq> 0" for m::nat
  using v_futr_pos i_nom_def by force

lemma i_nom_1[simp]: "$i^{1} = i"
  using v_futr_pos i_nom_def by force

lemma i_nom_eff: "(1 + $i^{m}/m)^m = 1 + i" if "m \<noteq> 0" for m::nat
  unfolding i_nom_def using less_imp_neq v_futr_pos that
  apply (simp, subst powr_realpow[THEN sym], simp)
  by (subst powr_powr, simp)

lemma i_nom_i: "1 + $i^{m}/m = (1+i).^(1/m)" if "m \<noteq> 0" for m::nat
  unfolding i_nom_def by (simp add: that)

lemma i_nom_0_iff_i_0: "$i^{m} = 0 \<longleftrightarrow> i = 0" if "m \<noteq> 0" for m::nat
proof
  assume "$i^{m} = 0"
  hence \<star>: "(1+i).^(1/m) = (1+i).^0"
    unfolding i_nom_def using v_futr_pos that by simp
  show "i = 0"
  proof (rule ccontr)
    assume "i \<noteq> 0"
    hence "1/m = 0" using powr_inj \<star> v_futr_pos by smt
    thus False using that by simp
  qed
next
  assume "i = 0"
  thus "$i^{m} = 0"
    unfolding i_nom_def by simp
qed

lemma i_nom_pos_iff_i_pos: "$i^{m} > 0 \<longleftrightarrow> i > 0" if "m \<noteq> 0" for m::nat
proof
  assume "$i^{m} > 0"
  hence \<star>: "(1+i).^(1/m) > 1.^(1/m)"
    unfolding i_nom_def using v_futr_pos that by (simp add: zero_less_mult_iff)
  thus "i > 0"
    using powr_less_cancel2[of "1/m" 1 "1+i"] v_futr_pos that by simp
next
  assume "i > 0"
  hence "(1+i).^(1/m) > 1.^(1/m)"
    using powr_less_mono2 v_futr_pos that by simp
  thus "$i^{m} > 0"
    unfolding i_nom_def using that by (simp add: zero_less_mult_iff)
qed

lemma e_delta: "exp $\<delta> = 1 + i"
  unfolding i_force_def by (simp add: v_futr_pos)

lemma delta_0_iff_i_0: "$\<delta> = 0 \<longleftrightarrow> i = 0"
proof
  assume "$\<delta> = 0"
  thus "i = 0"
    using e_delta by auto
next
  assume "i = 0"
  thus "$\<delta> = 0"
    unfolding i_force_def by simp
qed

lemma lim_i_nom: "(\<lambda>m. $i^{m}) \<longlonglongrightarrow> $\<delta>"
proof -
  let ?f = "\<lambda>h. ((1+i).^h - 1) / h"
  have D1ipwr: "DERIV (\<lambda>h. (1+i).^h) 0 :> $\<delta>"
    unfolding i_force_def
    using has_real_derivative_powr2[OF v_futr_pos, where x=0] v_futr_pos by simp
  hence limf: "(?f \<longlongrightarrow> $\<delta>) (at 0)"
    unfolding DERIV_def using v_futr_pos by auto
  hence "(\<lambda>m. $i^{Suc m}) \<longlonglongrightarrow> $\<delta>"
    unfolding i_nom_def using tendsto_at_iff_sequentially[of ?f "$\<delta>" 0 \<real>, THEN iffD1]
    apply simp
    apply (drule_tac x="\<lambda>m. 1 / Suc m" in spec, simp, drule mp)
    subgoal using lim_1_over_n LIMSEQ_Suc by force
    by (simp add: o_def mult.commute)
  thus ?thesis
    by (simp add: LIMSEQ_imp_Suc)
qed

lemma d_nom_0_iff_i_0: "$d^{m} = 0 \<longleftrightarrow> i = 0" if "m \<noteq> 0" for m::nat
proof -
  have "$d^{m} = 0 \<longleftrightarrow> $i^{m} = 0"
    unfolding d_nom_def using v_futr_m_pos by (smt (verit) divide_eq_0_iff of_nat_0)
  thus ?thesis
    using i_nom_0_iff_i_0 that by auto
qed

lemma d_nom_pos_iff_i_pos: "$d^{m} > 0 \<longleftrightarrow> i > 0" if "m \<noteq> 0" for m::nat
proof -
  have "$d^{m} > 0 \<longleftrightarrow> $i^{m} > 0"
    unfolding d_nom_def using zero_less_divide_iff i_nom_pos_iff_i_pos v_futr_m_pos that by smt
  thus ?thesis
    using i_nom_pos_iff_i_pos that by auto
qed

lemma d_nom_i_nom: "1 - $d^{m}/m = 1 / (1 + $i^{m}/m)" if "m \<noteq> 0" for m::nat
proof -
  have "1 - $d^{m}/m = 1 - ($i^{m}/m) / (1 + $i^{m}/m)"
    by (simp add: d_nom_def)
  also have "\<dots> = 1 / (1 + $i^{m}/m)"
    using v_futr_m_pos
    by (smt (verit, ccfv_SIG) add_divide_distrib that div_self)
  finally show ?thesis .
qed

lemma lim_d_nom: "(\<lambda>m. $d^{m}) \<longlonglongrightarrow> $\<delta>"
proof -
  have "(\<lambda>m. $i^{m}/m) \<longlonglongrightarrow> 0"
    using lim_i_nom tendsto_divide_0 tendsto_of_nat by blast
  hence "(\<lambda>m. 1 + $i^{m}/m) \<longlonglongrightarrow> 1"
    by (metis add.right_neutral tendsto_add_const_iff)
  thus ?thesis
    unfolding d_nom_def using lim_i_nom tendsto_divide div_by_1 by fastforce
qed

lemma v_pos: "$v > 0"
  unfolding v_pres_def using v_futr_pos by auto

lemma v_1_iff_i_0: "$v = 1 \<longleftrightarrow> i = 0"
proof
  assume "$v = 1"
  thus "i = 0"
    unfolding v_pres_def by simp
next
  assume "i = 0"
  thus "$v = 1"
    unfolding v_pres_def by simp
qed

lemma v_lt_1_iff_i_pos: "$v < 1 \<longleftrightarrow> i > 0"
proof
  assume "$v < 1"
  thus "i > 0"
    unfolding v_pres_def by (simp add: v_futr_pos)
next
  assume "i > 0"
  thus "$v < 1"
    unfolding v_pres_def by (simp add: v_futr_pos)
qed

lemma v_i_nom: "$v = (1 + $i^{m}/m).^-m" if "m \<noteq> 0" for m::nat
proof -
  have "$v = (1 + i).^-1"
    unfolding v_pres_def using v_futr_pos powr_real_def that by (simp add: powr_neg_one)
  also have "\<dots> = ((1 + $i^{m}/m)^m).^-1"
    using i_nom_eff that by presburger
  also have "\<dots> = (1 + $i^{m}/m).^-m"
    using powr_powr powr_realpow[THEN sym] v_futr_m_pos that by simp
  finally show ?thesis .
qed

lemma i_v: "1 + i = $v.^-1"
  unfolding v_pres_def powr_real_def using v_futr_pos powr_neg_one by simp

lemma i_v_powr: "(1 + i).^a = $v.^-a" for a::real
  by (subst i_v, subst powr_powr, simp)

lemma v_delta: "ln $v = - $\<delta>"
  unfolding i_force_def v_pres_def using v_futr_pos by (simp add: ln_div)

lemma is_derive_vpow: "DERIV (\<lambda>t. $v.^t) t :> - $\<delta> * $v.^t"
  using v_delta has_real_derivative_powr2 v_pos by (metis mult.commute)

lemma d_nom_v: "$d^{m} = m * (1 - $v.^(1/m))" if "m \<noteq> 0" for m::nat
proof -
  have "$d^{m} = m * (1 - 1 / (1 + $i^{m}/m))"
    using d_nom_i_nom[THEN sym] that by force
  also have "\<dots> = m * (1 - 1 / (1 + i).^(1/m))"
    using i_nom_i that powr_minus_divide by simp
  also have "\<dots> = m * (1 - $v.^(1/m))"
    using v_pres_def v_futr_pos powr_divide by simp
  finally show ?thesis .
qed

lemma d_nom_i_nom_v: "$d^{m} = $i^{m} * $v.^(1/m)" if "m \<noteq>0" for m::nat
  unfolding d_nom_def v_pres_def using i_nom_i powr_divide v_futr_pos that by auto

lemma a_calc: "$a^{m}_n = (1 - $v^n) / $i^{m}" if "m \<noteq> 0" "i \<noteq> 0" for n m ::nat
proof -
  have "\<And>l::nat. l/m = (1/m) * l" by simp
  hence \<star>: "\<And>l::nat. $v.^(l/m) = ($v.^(1/m))^l"
    using powr_powr powr_realpow v_pos by (metis powr_gt_zero)
  hence "$a^{m}_n = (\<Sum>k<n*m. ($v.^(1/m))^(k+1::nat) / m)"
    unfolding ann_def by presburger
  also have "\<dots> = $v.^(1/m) * (\<Sum>k<n*m. ($v.^(1/m))^k) / m"
    by (simp, subst sum_divide_distrib[THEN sym], subst sum_distrib_left[THEN sym], simp)
  also have "\<dots> = $v.^(1/m) * ((($v.^(1/m))^(n*m) - 1) / ($v.^(1/m) - 1)) / m"
    apply (subst geometric_sum[of "$v.^(1/m)" "n*m"]; simp?)
    using powr_zero_eq_one[of "$v"] v_pos v_1_iff_i_0 powr_inj that
    by (smt (verit, del_insts) divide_eq_0_iff of_nat_eq_0_iff)
  also have "\<dots> = (($v.^(1/m))^(n*m) - 1) / (m * ($v.^(1/m) - 1) / $v.^(1/m))"
    by (simp add: field_simps)
  also have "\<dots> = ($v^n - 1) / (m * (1 - 1 / $v.^(1/m)))"
    apply (subst \<star>[of "n*m::nat", THEN sym], simp only: of_nat_simps)
    apply (subst nonzero_mult_div_cancel_right[where 'a=real, of m n], simp add: that)
    apply (subst powr_realpow[OF v_pos])
    apply (subst times_divide_eq_right[of _ _ "$v.^(1/m)", THEN sym])
    using v_pos by (subst diff_divide_distrib[of _ _ "$v.^(1/m)"], simp)
  also have "\<dots> = (1 - $v^n) / (m * (1 / $v.^(1/m) - 1))"
    using minus_divide_divide by (smt mult_minus_right)
  also have "\<dots> = (1 - $v^n) / $i^{m}"
    unfolding i_nom_def v_pres_def using v_futr_pos powr_divide by auto
  finally show ?thesis .
qed

lemma a_calc_i_0: "$a^{m}_n = n" if "m \<noteq> 0" "i = 0" for n m :: nat 
  unfolding ann_def v_pres_def using that by simp

lemma s_calc_i_0: "$s^{m}_n = n" if "m \<noteq> 0" "i = 0" for n m :: nat
  unfolding acc_def using that by simp

lemma s_a: "$s^{m}_n = (1+i)^n * $a^{m}_n" if "m \<noteq> 0" for n m :: nat
proof -
  have "(1+i)^n * $a^{m}_n = (\<Sum>k<n*m. (1+i)^n * ($v.^((k+1::nat)/m) / m))"
    unfolding ann_def using sum_distrib_left by blast
  also have "\<dots> = (\<Sum>k<n*m. (1+i).^((n*m - Suc k)/m) / m)"
  proof -
    have "\<And>k::nat. k < n*m \<Longrightarrow> (1+i)^n * ($v.^((k+1::nat)/m) / m) = (1+i).^((n*m - Suc k)/m) / m"
      unfolding v_pres_def
      apply (subst powr_realpow[THEN sym], simp add: v_futr_pos)
      apply (subst inverse_powr, simp add: v_futr_pos)
      apply (subst times_divide_eq_right, subst powr_add[THEN sym], simp add: that)
      by (subst of_nat_diff, simp add: Suc_le_eq, simp add: diff_divide_distrib that)
    thus ?thesis by (meson lessThan_iff sum.cong)
  qed
  also have "\<dots> = (\<Sum>k<n*m. (1+i).^(k/m) / m)"
    apply (subst atLeast0LessThan[THEN sym])+
    by (subst sum.atLeastLessThan_rev[THEN sym, of _ "n*m" 0, simplified add_0_right], simp)
  also have "\<dots> = $s^{m}_n"
    unfolding acc_def by simp
  finally show ?thesis ..
qed

lemma s_calc: "$s^{m}_n = ((1+i)^n - 1) / $i^{m}" if "m \<noteq> 0" "i \<noteq> 0" for n m :: nat
  using that v_futr_pos
  apply (subst s_a, simp, subst a_calc; simp?)
  apply (rule disjI2)
  apply (subst right_diff_distrib, simp)
  apply (rule left_right_inverse_power)
  unfolding v_pres_def by auto

lemma a''_a: "$a''^{m}_n = (1+i).^(1/m) * $a^{m}_n" if "m \<noteq> 0" for m::nat
  unfolding ann_def ann_due_def
  apply (subst sum_distrib_left, subst times_divide_eq_right, simp)
  by (subst i_v, subst powr_powr, subst powr_add[THEN sym], simp, subst add_divide_distrib, simp)

lemma a_a'': "$a^{m}_n = $v.^(1/m) * $a''^{m}_n" if "m \<noteq> 0" for m::nat
  unfolding ann_def ann_due_def
  apply (subst sum_distrib_left, subst times_divide_eq_right, simp)
  by (subst powr_add[THEN sym], subst add_divide_distrib, simp)

lemma a''_calc_i_0: "$a''^{m}_n = n" if "m \<noteq> 0" "i = 0" for n m :: nat
  unfolding ann_due_def v_pres_def using that by simp

lemma s''_calc_i_0: "$s''^{m}_n = n" if "m \<noteq> 0" "i = 0" for n m :: nat
  unfolding acc_due_def using that by simp

lemma a''_calc: "$a''^{m}_n = (1 - $v^n) / $d^{m}" if "m \<noteq> 0" "i \<noteq> 0" for n m :: nat
proof -
  have "$a''^{m}_n = (1+i).^(1/m) * ((1 - $v^n) / $i^{m})"
    using a''_a a_calc times_divide_eq_right that by simp
  also have "\<dots> = (1 - $v^n) / ($v.^(1/m) * $i^{m})"
    by (subst i_v, subst powr_powr, simp, subst powr_minus_divide, simp)
  also have "\<dots> = (1 - $v^n) / $d^{m}"
    using d_nom_i_nom_v that by simp
  finally show ?thesis .
qed

lemma s''_s: "$s''^{m}_n = (1+i).^(1/m) * $s^{m}_n" if "m \<noteq> 0" for m::nat
  unfolding acc_def acc_due_def
  apply (subst sum_distrib_left, subst times_divide_eq_right)
  by (subst powr_add[THEN sym], simp, subst add_divide_distrib, simp)

lemma s_s'': "$s^{m}_n = $v.^(1/m) * $s''^{m}_n" if "m \<noteq> 0" for m::nat
  unfolding acc_def acc_due_def v_pres_def using v_futr_pos
  apply (subst sum_distrib_left, subst times_divide_eq_right, simp)
  by (subst inverse_powr, simp, subst powr_add[THEN sym], subst add_divide_distrib, simp)

lemma s''_calc: "$s''^{m}_n = ((1+i)^n - 1) / $d^{m}" if "m \<noteq> 0" "i \<noteq> 0" for n m :: nat
proof -
  have "$s''^{m}_n = (1+i).^(1/m) * ((1+i)^n - 1) / $i^{m}"
    using s''_s s_calc times_divide_eq_right that by simp
  also have "\<dots> = ((1+i)^n - 1) / ($v.^(1/m) * $i^{m})"
    by (subst i_v, subst powr_powr, simp, subst powr_minus_divide, simp)
  also have "\<dots> = ((1+i)^n - 1) / $d^{m}"
    using d_nom_i_nom_v that by simp
  finally show ?thesis .
qed

lemma s''_a'': "$s''^{m}_n = (1+i)^n * $a''^{m}_n" if "m \<noteq> 0" for m::nat
  using that s''_s a''_a s_a by simp

lemma a'_calc: "$a'_n = (1 - $v.^n) / $\<delta>" if "i \<noteq> 0" "n \<ge> 0" for n::real
  unfolding ann_cont_def
  apply (rule integral_unique)
  using has_integral_powr2_from_0[OF v_pos _ that(2)] v_delta v_1_iff_i_0 that
  by (smt minus_divide_divide)

lemma a'_calc_i_0: "$a'_n = n" if "i = 0" "n \<ge> 0" for n::real
  unfolding ann_cont_def
  apply (subst iffD2[OF v_1_iff_i_0], simp add: that)
  by (simp add: integral_cong that)

lemma s'_calc: "$s'_n = ((1+i).^n - 1) / $\<delta>" if "i \<noteq> 0" "n \<ge> 0" for n::real
  unfolding acc_cont_def
  apply (rule integral_unique)
  using has_integral_powr2_from_0[OF v_futr_pos _ that(2)] i_force_def that
  by simp

lemma s'_calc_i_0: "$s'_n = n" if "i = 0" "n \<ge> 0" for n::real
  unfolding acc_cont_def
  apply (subst \<open>i = 0\<close>, simp)
  by (simp add: integral_cong that)

lemma s'_a': "$s'_n = (1+i).^n * $a'_n" if "n \<ge> 0" for n::real
proof -
  have "(1+i).^n * $a'_n = integral {0..n} (\<lambda>t. (1+i).^(n-t))"
    unfolding ann_cont_def
    using integrable_on_powr2_from_0_general[of "$v" n] v_pos v_futr_pos that
    apply (subst integral_mult, simp)
    apply (rule integral_cong)
    unfolding v_pres_def using inverse_powr powr_add[THEN sym] by smt
  also have "\<dots> = $s'_n"
    unfolding acc_cont_def using v_futr_pos that
    apply (subst has_integral_interval_reverse[of 0 n, simplified, THEN integral_unique]; simp?)
    by (rule continuous_on_powr; auto)
  finally show ?thesis ..
qed

lemma lim_m_a: "(\<lambda>m. $a^{m}_n) \<longlonglongrightarrow> $a'_n" for n::nat
proof (rule LIMSEQ_imp_Suc)
  show "(\<lambda>m. $a^{Suc m}_n) \<longlonglongrightarrow> $a'_n"
  proof (cases "i = 0")
    case True
    show ?thesis
      using a_calc_i_0 a'_calc_i_0 True by simp
  next
    case False
    show ?thesis
      using False v_pos delta_0_iff_i_0
      apply (subst a_calc; simp?)
      apply (subst a'_calc; simp?)
      apply (subst powr_realpow, simp)
      apply (rule tendsto_divide; simp?)
      by (rule LIMSEQ_Suc[OF lim_i_nom])
  qed
qed

lemma lim_m_a'': "(\<lambda>m. $a''^{m}_n) \<longlonglongrightarrow> $a'_n" for n::nat
proof (rule LIMSEQ_imp_Suc)
  show "(\<lambda>m. $a''^{Suc m}_n) \<longlonglongrightarrow> $a'_n"
  proof (cases "i = 0")
    case True
    show ?thesis
      using a''_calc_i_0 a'_calc_i_0 True by simp
  next
    case False
    show ?thesis
      using False v_pos delta_0_iff_i_0
      apply (subst a''_calc; simp?)
      apply (subst a'_calc; simp?)
      apply (subst powr_realpow, simp)
      apply (rule tendsto_divide; simp?)
      by (rule LIMSEQ_Suc[OF lim_d_nom])
  qed
qed

lemma lim_m_s: "(\<lambda>m. $s^{m}_n) \<longlonglongrightarrow> $s'_n" for n::nat
proof (rule LIMSEQ_imp_Suc)
  show "(\<lambda>m. $s^{Suc m}_n) \<longlonglongrightarrow> $s'_n"
  proof (cases "i = 0")
    case True
    show ?thesis
      using s_calc_i_0 s'_calc_i_0 True by simp
  next
    case False
    show ?thesis
      using False v_futr_pos delta_0_iff_i_0
      apply (subst s_calc; simp?)
      apply (subst s'_calc; simp?)
      apply (subst powr_realpow, simp)
      apply (rule tendsto_divide; simp?)
      by (rule LIMSEQ_Suc[OF lim_i_nom])
  qed
qed

lemma lim_m_s'': "(\<lambda>m. $s''^{m}_n) \<longlonglongrightarrow> $s'_n" for n::nat
proof (rule LIMSEQ_imp_Suc)
  show "(\<lambda>m. $s''^{Suc m}_n) \<longlonglongrightarrow> $s'_n"
  proof (cases "i = 0")
    case True
    show ?thesis
      using s''_calc_i_0 s'_calc_i_0 True by simp
  next
    case False
    show ?thesis
      using False v_futr_pos delta_0_iff_i_0
      apply (subst s''_calc; simp?)
      apply (subst s'_calc; simp?)
      apply (subst powr_realpow, simp)
      apply (rule tendsto_divide; simp?)
      by (rule LIMSEQ_Suc[OF lim_d_nom])
  qed
qed

lemma lim_n_a: "(\<lambda>n. $a^{m}_n) \<longlonglongrightarrow> $a^{m}_\<infinity>" if "m \<noteq> 0" "i > 0" for m::nat
proof -
  have "$i^{m} \<noteq> 0" using i_nom_pos_iff_i_pos that by smt
  moreover have "(\<lambda>n. $v^n) \<longlonglongrightarrow> 0"
    using LIMSEQ_realpow_zero[of "$v"] v_pos v_lt_1_iff_i_pos that by simp
  ultimately show ?thesis
    using that apply (subst a_calc; simp?)
    unfolding perp_def apply (rule tendsto_divide; simp?)
    using tendsto_diff[where a=1 and b=0] by auto
qed

lemma lim_n_a'': "(\<lambda>n. $a''^{m}_n) \<longlonglongrightarrow> $a''^{m}_\<infinity>" if "m \<noteq> 0" "i > 0" for m::nat
proof -
  have "$d^{m} \<noteq> 0" using d_nom_pos_iff_i_pos that by smt
  moreover have "(\<lambda>n. $v^n) \<longlonglongrightarrow> 0"
    using LIMSEQ_realpow_zero[of "$v"] v_pos v_lt_1_iff_i_pos that by simp
  ultimately show ?thesis
    using that apply (subst a''_calc; simp?)
    unfolding perp_due_def apply (rule tendsto_divide; simp?)
    using tendsto_diff[where a=1 and b=0] by auto
qed

lemma Ilsm_Ilam: "$(I^{l}s)^{m}_n = (1+i)^n * $(I^{l}a)^{m}_n"
  if "l \<noteq> 0" "m \<noteq> 0" for l n m :: nat
  unfolding acc_incr_def ann_incr_def v_pres_def using v_futr_pos powr_realpow
  apply (subst inverse_powr, simp)
  apply (subst sum_distrib_left)
  by (subst minus_real_def, subst powr_add, subst times_divide_eq_right, subst mult.assoc, simp)

lemma Iam_calc: "$(Ia)^{m}_n = (\<Sum>j<n. (j+1)/m * (\<Sum>k=j*m..<(j+1)*m. $v.^((k+1)/m)))"
  if "m \<noteq> 0" for n m :: nat
proof -
  let ?I = "{..<n}"
  let ?A = "\<lambda>j. {j*m..<(j+1)*m}"
  let ?g = "\<lambda>k. $v.^((k+1::nat)/m) * \<lceil>(k+1::nat)/m\<rceil> / m"
  have "$(Ia)^{m}_n = (\<Sum>j<n. \<Sum>k=j*m..<(j+1)*m. $v.^((k+1)/m) * \<lceil>(k+1)/m\<rceil> / m)"
    unfolding ann_incr_def using seq_part_multiple that
    apply (simp only: mult_1)
    by (subst sum.UNION_disjoint[of ?I ?A ?g, THEN sym]; simp)
  also have "\<dots> = (\<Sum>j<n. (j+1)/m * (\<Sum>k=j*m..<(j+1)*m. $v.^((k+1)/m)))"
  proof -
    { fix j k
      assume "j*m \<le> k \<and> k < (j+1)*m"
      hence "j*m < k+1 \<and> k+1 \<le> (j+1)*m" by force
      hence "j < (k+1)/m \<and> (k+1)/m \<le> j+1"
        using pos_less_divide_eq pos_divide_le_eq of_nat_less_iff of_nat_le_iff that
        by (smt (verit) of_nat_le_0_iff of_nat_mult)
      hence "\<lceil>(k+1)/m\<rceil> = j+1"
        by (simp add: ceiling_unique) }
    hence "\<And>j k. j*m \<le> k \<and> k < (j+1)*m \<Longrightarrow> \<lceil>(k+1)/m\<rceil> = j+1"
      by (metis (no_types) of_nat_1 of_nat_add)
    with v_pos show ?thesis
      apply -
      apply (rule sum.cong, simp)
      apply (subst sum_distrib_left, rule sum.cong; simp)
      by (smt (verit, ccfv_SIG) of_int_1 of_int_diff of_int_of_nat_eq)
  qed
  finally show ?thesis .
qed

lemma Ism_calc: "$(Is)^{m}_n = (\<Sum>j<n. (j+1)/m * (\<Sum>k=j*m..<(j+1)*m. (1+i).^(n-(k+1)/m)))"
  if "m \<noteq> 0" for n m :: nat
  using v_pos that
  apply (subst Ilsm_Ilam; simp)
  apply (subst Iam_calc[simplified]; simp?)
  apply ((subst sum_distrib_left, rule sum.cong; simp))+
  unfolding v_pres_def using v_futr_pos
  apply (subst inverse_powr; simp)
  apply (subst powr_realpow[THEN sym], simp)
  by (subst powr_add[THEN sym]; simp)

lemma Imam_calc_aux: "$(I^{m}a)^{m}_n = (\<Sum>k<n*m. $v.^((k+1)/m) * (k+1) / m^2)"
  if "m \<noteq> 0" for m::nat
  unfolding ann_incr_def power_def
  apply (rule sum.cong, simp)
  apply (subst of_nat_mult)
  using v_pos that
  apply (subst nonzero_mult_div_cancel_left, simp)
  by (subst ceiling_of_nat; simp)

lemma Imam_calc:
  "$(I^{m}a)^{m}_n = ($v.^(1/m) * (1 - (n*m+1)*$v^n + n*m*$v.^(n+1/m))) / (m*(1-$v.^(1/m)))^2"
  if "i \<noteq> 0" "m \<noteq> 0" for n m :: nat
proof -
  have \<star>: "$v.^(1/m) > 0" using v_pos by force
  hence "$(I^{m}a)^{m}_n = (\<Sum>k<n*m. (k+1)*($v.^(1/m))^(k+1)) / m^2"
    using that
    apply (subst Imam_calc_aux, simp)
    apply (subst sum_divide_distrib[THEN sym], simp)
    apply (rule sum.cong; simp)
    using powr_realpow[THEN sym] powr_powr by (simp add: add_divide_distrib powr_add)
  also have "\<dots> = $v.^(1/m) * (\<Sum>k<n*m. (k+1)*($v.^(1/m))^k) / m^2"
    by (subst sum_distrib_left, simp add: that, rule sum.cong; simp)
  also have "\<dots> = $v.^(1/m) *
    ((1 - (n*m+1)*($v.^(1/m))^(n*m) + n*m*($v.^(1/m))^(n*m+1)) / (1 - $v.^(1/m))^2) / m^2"
    using v_pos v_1_iff_i_0 that by (subst geometric_increasing_sum; simp?)
  also have "\<dots> = ($v.^(1/m) * (1 - (n*m+1)*$v^n + n*m*$v.^(n+1/m))) / (m*(1-$v.^(1/m)))^2"
    using \<star>
    apply (subst powr_realpow[of "$v.^(1/m)", THEN sym], simp)+
    apply (subst powr_powr)+
    apply (subst times_divide_eq_right[THEN sym], subst divide_divide_eq_left)
    apply (subst power_mult_distrib)
    using powr_eq_one_iff_gen v_pos v_1_iff_i_0 apply (simp add: field_simps)
    by ((subst powr_realpow, simp)+, simp)
  finally show ?thesis .
qed

lemma Imam_calc_i_0: "$(I^{m}a)^{m}_n = (n*m+1)*n / (2*m)" if "i = 0" "m \<noteq> 0" for n m :: nat
proof -
  have "$(I^{m}a)^{m}_n = (\<Sum>k<n*m. $v.^((k+1)/m) * (k+1) / m^2)"
    by (subst Imam_calc_aux, simp_all add: that)
  also have "\<dots> = (\<Sum>k<n*m. k+1) / m^2"
    apply (subst v_1_iff_i_0[THEN iffD2], simp_all add: that)
    by (subst sum_divide_distrib[THEN sym], simp)
  also have "\<dots> = (n*m*(n*m+1) div 2) / m^2"
    apply (subst Suc_eq_plus1[THEN sym], subst sum_bounds_lt_plus1[of id, simplified])
    by (subst Sum_Icc_nat, simp)
  also have "\<dots> = (n*m+1)*n / (2*m)"
    apply (subst real_of_nat_div, simp)
    using that by (subst power2_eq_square, simp add: field_simps)
  finally show ?thesis .
qed

lemma Imsm_calc:
  "$(I^{m}s)^{m}_n = ((1+i).^(n+1/m) - (n*m+1)*(1+i).^(1/m) + n*m) / (m*((1+i).^(1/m)-1))^2"
  if "i \<noteq> 0" "m \<noteq> 0" for n m :: nat
proof -
  have "$(I^{m}a)^{m}_n =
    ($v^n * ((1+i).^(n+1/m) - (n*m+1)*(1+i).^(1/m) + n*m)) / (m*((1+i).^(1/m)-1))^2"
  proof -
    have "$(I^{m}a)^{m}_n =
      ($v.^(1/m) * (1 - (n*m+1)*$v^n + n*m*$v.^(n+1/m))) / (m*(1-$v.^(1/m)))^2"
      using that by (subst Imam_calc; simp)
    also have "\<dots> = (1 - (n*m+1)*$v^n + n*m*$v.^(n+1/m)) / ($v.^(1/m)*(m*($v.^(-1/m)-1))^2)"
      apply (subgoal_tac "$v.^(-1/m) = 1 / $v.^(1/m)", erule ssubst)
       apply ((subst power2_eq_square)+, simp add: field_simps that)
      by (simp add: powr_minus_divide)
    also have "\<dots> =
      ($v.^(n+1/m) * ($v.^(-n-1/m) - (n*m+1)*$v.^(-1/m) + n*m)) / ($v.^(1/m)*(m*($v.^(-1/m)-1))^2)"
      apply (subgoal_tac "$v.^(-n-1/m) = 1 / $v.^(n+1/m)" "$v.^(-1/m) = $v^n / $v.^(n+1/m)")
        apply ((erule ssubst)+, simp_all add: field_simps)
      using v_pos
       apply (simp add: powr_diff[THEN sym] powr_realpow[THEN sym])
      by (smt powr_minus_divide)
    also have "\<dots> =
      ($v^n * ($v.^(-n-1/m) - (n*m+1)*$v.^(-1/m) + n*m)) / ((m*($v.^(-1/m)-1))^2)"
      apply (subst powr_add[of _ n "1/m"])
      using v_pos powr_realpow by simp
    also have "\<dots> =
      ($v^n * ((1+i).^(n+1/m) - (n*m+1)*(1+i).^(1/m) + n*m)) / ((m*((1+i).^(1/m)-1))^2)"
      apply (subgoal_tac "-n-1/m = -(n+1/m)" "-1/m = -(1/m)", (erule ssubst)+)
        apply (subst i_v_powr[THEN sym])+
      by simp_all
    finally show ?thesis .
  qed
  thus ?thesis
    apply -
    using that v_futr_pos
    apply (subst Ilsm_Ilam, simp)
    apply (erule ssubst, simp)
    apply (rule disjI2)
    by (subst power_mult_distrib[THEN sym], simp add: v_pres_def)
qed

lemma Imsm_calc_i_0: "$(I^{m}s)^{m}_n = (n*m+1)*n / (2*m)" if "i = 0" "m \<noteq> 0" for n m :: nat
  using that
  apply (subst Ilsm_Ilam, simp)
  by (subst Imam_calc_i_0; simp)

lemma Ila''m_Ilam: "$(I^{l}a'')^{m}_n = (1+i).^(1/m) * $(I^{l}a)^{m}_n"
  if "l \<noteq> 0" "m \<noteq> 0" for l m n :: nat
  unfolding ann_incr_def ann_due_incr_def using that
  apply (subst i_v, subst powr_powr, simp)
  apply (subst sum_distrib_left)
  apply (rule sum.cong; simp)
  apply (rule disjI2)
  by (smt (verit) add_divide_distrib powr_add)

lemma Ia''m_calc: "$(Ia'')^{m}_n = (\<Sum>j<n. (j+1)/m * (\<Sum>k=j*m..<(j+1)*m. $v.^(k/m)))"
  if "m \<noteq> 0" for n m :: nat
  using that
  apply (subst Ila''m_Ilam; simp del: One_nat_def)
  apply (subst Iam_calc; simp)
  apply (subst sum_distrib_left)
  apply (rule sum.cong; simp)
  apply (subst sum_distrib_left)+
  apply (rule sum.cong; simp)
  apply (subst i_v_powr)
  using powr_add[of "$v", THEN sym] by (simp add: field_simps)

lemma Ima''m_calc_aux: "$(I^{m}a'')^{m}_n = (\<Sum>k<n*m. $v.^(k/m) * (k+1) / m^2)"
  if "m \<noteq> 0" for m::nat
  using that
  apply (subst Ila''m_Ilam, simp)
  apply (subst Imam_calc_aux, simp)
  apply (subst sum_distrib_left)
  apply (rule sum.cong; simp)
  using powr_add[of "$v", THEN sym] i_v_powr by (simp add: field_simps)

lemma Ima''m_calc: "$(I^{m}a'')^{m}_n = (1 - (n*m+1)*$v^n + n*m*$v.^(n+1/m)) / (m*(1-$v.^(1/m)))^2"
  if "i \<noteq> 0" "m \<noteq> 0" for n m :: nat
  using that v_pos
  apply (subst Ila''m_Ilam, simp)
  apply (subst Imam_calc; simp)
  apply (rule disjI2)+
  by (subst i_v, subst powr_powr, subst powr_add[THEN sym], simp)

lemma Ils''m_Ilsm: "$(I^{l}s'')^{m}_n = (1+i).^(1/m) * $(I^{l}s)^{m}_n"
  if "l \<noteq> 0" "m \<noteq> 0" for l m n :: nat
  unfolding acc_incr_def acc_due_incr_def using that
  apply (subst sum_distrib_left)
  apply (rule sum.cong; simp)
  apply (rule disjI2)
  by (subst powr_add[THEN sym], subst add_divide_distrib, simp)

lemma Ims''m_calc:
  "$(I^{m}s'')^{m}_n =
    (1+i).^(1/m) * ((1+i).^(n+1/m) - (n*m+1)*(1+i).^(1/m) + n*m) / (m*((1+i).^(1/m)-1))^2"
  if "i \<noteq> 0" "m \<noteq> 0" for n m :: nat
  using that by (simp add: Ils''m_Ilsm Imsm_calc)

lemma lim_Imam: "(\<lambda>n. $(I^{m}a)^{m}_n) \<longlonglongrightarrow> 1 / ($i^{m}*$d^{m})" if "m \<noteq> 0" "i > 0" for m::nat
proof -
  have "(\<lambda>n. $(I^{m}a)^{m}_n) = 
    (\<lambda>n. $v.^(1/m) * (1 - (n*m+1)*$v^n + n*m*$v.^(n+1/m)) / (m*(1-$v.^(1/m)))^2)"
    using that by (subst Imam_calc; simp)
  moreover have "(\<lambda>n. $v.^(1/m) * (1 - (n*m+1)*$v^n + n*m*$v.^(n+1/m)) / (m*(1-$v.^(1/m)))^2)
    \<longlonglongrightarrow> 1 / ($i^{m}*$d^{m})"
  proof -
    have \<star>: "\<bar>$v\<bar> < 1"
      using v_lt_1_iff_i_pos v_pos that by force
    hence "(\<lambda>n. (n*m+1)*$v^n) \<longlonglongrightarrow> 0"
      apply (subst tendsto_cong[of _ "(\<lambda>n. n*m*$v^n + $v^n)"])
       apply (rule always_eventually, rule allI)
       apply (simp add: distrib_right)
      apply (subgoal_tac "0 = 0 + 0", erule ssubst, intro tendsto_intros; simp)
      apply (subst mult.commute, subst mult.assoc)
      apply (subgoal_tac "0 = real m * 0", erule ssubst, intro tendsto_intros; simp?)
      by (rule powser_times_n_limit_0; simp)
    moreover have "(\<lambda>n. n*m*$v.^(n+1/m)) \<longlonglongrightarrow> 0"
      apply (subst tendsto_cong[of _ "(\<lambda>n. (m*$v.^(1/m))*(n*$v^n))"])
       apply (rule always_eventually, rule allI)
       apply (subst powr_add, subst powr_realpow; simp add: v_pos)
      apply (subgoal_tac "0 = m*$v.^(1/m) * 0", erule ssubst, intro tendsto_intros; simp?)
      by (rule powser_times_n_limit_0, simp add: \<star>)
    ultimately have "(\<lambda>n. $v.^(1/m) * (1 - (n*m+1)*$v^n + n*m*$v.^(n+1/m)) / (m*(1-$v.^(1/m)))^2)
      \<longlonglongrightarrow> $v.^(1/m) * (1 - 0 + 0)/ (m*(1-$v.^(1/m)))^2"
      using v_lt_1_iff_i_pos v_pos that by (intro tendsto_intros; simp)
    thus ?thesis
      unfolding i_nom_def using v_pos that
      apply (subst i_v_powr, subst powr_minus_divide, subst d_nom_v; simp)
      by (subst(asm)(2) power2_eq_square, simp add: field_simps)
  qed
  ultimately show ?thesis by simp
qed

lemma perp_incr_calc: "$(I^{m}a)^{m}_\<infinity> = 1 / ($i^{m}*$d^{m})" if "m \<noteq> 0" "i > 0" for m::nat
  unfolding perp_incr_def by (rule limI, rule lim_Imam; simp add: that)

lemma lim_Ima''m: "(\<lambda>n. $(I^{m}a'')^{m}_n) \<longlonglongrightarrow> 1 / ($d^{m})^2" if "m \<noteq> 0" "i > 0" for m::nat
  unfolding perp_due_incr_def using that
  apply (subst Ila''m_Ilam, simp, subst mult.commute, subst i_v_powr, subst powr_minus_divide)
  apply (subgoal_tac "1/($d^{m})^2 = (1/($i^{m}*$d^{m}))*(1/$v.^(1/m))", erule ssubst)
   apply (intro tendsto_intros, simp add: lim_Imam)
  by (subst power2_eq_square, subst(1) d_nom_i_nom_v; simp add: field_simps that)

lemma perp_due_incr_calc: "$(I^{m}a'')^{m}_\<infinity> = 1 / ($d^{m})^2" if "m \<noteq> 0" "i > 0" for m::nat
  unfolding perp_due_incr_def by (rule limI, rule lim_Ima''m; simp add: that)

end

end
