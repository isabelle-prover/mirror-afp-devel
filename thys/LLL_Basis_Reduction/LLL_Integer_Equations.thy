(*
    Authors:    René Thiemann
    License:    BSD
*)
subsection \<open>LLL Implementation based on Integer Arithmetic\<close>

text \<open>In this part we aim to update the integer values $d\,(j+1) * \mu_{i,j}$ as well as the 
  Gramian determinants $d\,i$. \<close>

subsubsection \<open>Updates of the integer values for Swap, Add, etc.\<close>

text \<open>We provide equations how to implement the LLL-algorithm by storing the integer values
  $d\, (j+1) * \mu_{i,j}$ and all $d\ i$ in addition to the vectors in $f$.
  Moreover, we show how to check condition like the one on norms via the integer values.\<close>

theory LLL_Integer_Equations
  imports
   LLL
   LLL_Number_Bounds
begin


context LLL
begin

lemma d_d\<mu>_add_row: assumes Linv: "LLL_invariant True i fs"
  and i: "i < m"  and j: "j < i" 
  and c: "c = floor_ceil (\<mu> fs i j)" 
  and fs': "fs' = fs[ i := fs ! i - c \<cdot>\<^sub>v fs ! j]" 
  and mu_small: "\<mu>_small_row i fs (Suc j)" 
shows  
  (* d-updates: none *)
  "\<And> ii. ii \<le> m \<Longrightarrow> d fs' ii = d fs ii" 
  (* d\<mu>-updates: *)
  "\<And> i' j'. i' < m \<Longrightarrow> j' < i' \<Longrightarrow>       
     d\<mu> fs' i' j' = (
       if i' = i \<and> j' < j 
         then d\<mu> fs i' j' - c * d\<mu> fs j j' 
       else if i' = i \<and> j' = j 
         then d\<mu> fs i' j' - c * d fs (Suc j) 
       else d\<mu> fs i' j')"
    (is "\<And> i' j'. _ \<Longrightarrow> _ \<Longrightarrow> _ = ?new_mu i' j'")
proof -
  interpret fs: fs_int' n m fs_init \<alpha> True i fs
    by standard (use Linv in auto)
  note add = basis_reduction_add_row_main[OF Linv i j c fs' mu_small]
  interpret fs': fs_int' n m fs_init \<alpha> True i fs'
    by standard (use add in auto)
  show d: "\<And> ii. ii \<le> m \<Longrightarrow> d fs' ii = d fs ii" by fact
  fix i' j'
  assume i': "i' < m" and j': "j' < i'"    
  hence j'm: "j' < m" and j'': "j' \<le> i'" by auto
  note updates = add(5)[OF i' j'm]
  show "d\<mu> fs' i' j' = ?new_mu i' j'" 
  proof (cases "i' = i")
    case False
    thus ?thesis using d i' j' unfolding d\<mu>_def updates by auto
  next
    case True
    have id': "d fs' (Suc j') = d fs (Suc j')" by (rule d, insert i' j', auto)
    note fs'.d\<mu>[]
    have *: "rat_of_int (d\<mu> fs' i' j') = rat_of_int (d fs' (Suc j')) * fs'.gs.\<mu> i' j'"
      unfolding d\<mu>_def d_def
      apply(rule fs'.d\<mu>[unfolded fs'.d\<mu>_def fs'.d_def])
      using j' i'  LLL_invD[OF add(1)]  by (auto)
    have **: "rat_of_int (d\<mu> fs i' j') = rat_of_int (d fs (Suc j')) * fs.gs.\<mu> i' j'"
      unfolding d\<mu>_def d_def
      apply(rule fs.d\<mu>[unfolded fs.d\<mu>_def fs.d_def])
      using j' i' LLL_invD[OF Linv]  by (auto)
    have ***: "rat_of_int (d\<mu> fs j j') = rat_of_int (d fs (Suc j')) * fs.gs.\<mu> j j'" if "j' < j"
      unfolding d\<mu>_def d_def
      apply(rule fs.d\<mu>[unfolded fs.d\<mu>_def fs.d_def])
      using that j i LLL_invD[OF Linv]  by (auto)

    show ?thesis
      apply(intro int_via_rat_eqI)
      apply(unfold if_distrib[of rat_of_int] of_int_diff of_int_mult ** * updates id' ring_distribs)
      apply(insert True i' j' i j)
      by(auto simp: fs.gs.\<mu>.simps algebra_simps ***)
  qed
qed

end

context LLL_with_assms
begin
lemma d_d\<mu>_swap: assumes inv: "LLL_invariant False i fs"
  and i: "i < m"
  and i0: "i \<noteq> 0" 
  and norm_ineq: "sq_norm (gso fs (i - 1)) > \<alpha> * sq_norm (gso fs i)" 
  and fs'_def: "fs' = fs[i := fs ! (i - 1), i - 1 := fs ! i]" 
shows (* d-updates *)
  "\<And> ii. ii \<le> m \<Longrightarrow>
      d fs' ii = (
        if ii = i then 
          (d fs (Suc i) * d fs (i - 1) + d\<mu> fs i (i - 1) * d\<mu> fs i (i - 1)) div d fs i 
        else d fs ii)"
and (* d\<mu>-updates *)
  "\<And> ii j. ii < m \<Longrightarrow> j < ii \<Longrightarrow> 
      d\<mu> fs' ii j = (
        if ii = i - 1 then 
           d\<mu> fs i j
        else if ii = i \<and> j \<noteq> i - 1 then 
             d\<mu> fs (i - 1) j
        else if ii > i \<and> j = i then
           (d fs (Suc i) * d\<mu> fs ii (i - 1) - d\<mu> fs i (i - 1) * d\<mu> fs ii j) div d fs i
        else if ii > i \<and> j = i - 1 then 
           (d\<mu> fs i (i - 1) * d\<mu> fs ii j + d\<mu> fs ii i * d fs (i - 1)) div d fs i
        else d\<mu> fs ii j)" 
    (is "\<And> ii j. _ \<Longrightarrow> _ \<Longrightarrow> _ = ?new_mu ii j")
proof -
  note swap = basis_reduction_swap[OF inv i i0 norm_ineq fs'_def]
  from i i0 have ii: "i - 1 < i" and le_m: "i - 1 \<le> m" "i \<le> m" "Suc i \<le> m" by auto
  from LLL_invD[OF inv] have len: "length fs = m" by auto
  interpret fs: fs_int' n m fs_init \<alpha> False i fs
    by standard (use inv in auto)
  interpret fs': fs_int' n m fs_init \<alpha> False "i - 1" fs'
    by standard (use swap(1) in auto)
  let ?r = rat_of_int
  let ?n = "\<lambda> i. sq_norm (gso fs i)" 
  let ?n' = "\<lambda> i. sq_norm (gso fs' i)" 
  let ?dn = "\<lambda> i. ?r (d fs i * d fs i) * ?n i" 
  let ?dn' = "\<lambda> i. ?r (d fs' i * d fs' i) * ?n' i" 
  let ?dmu = "\<lambda> i j. ?r (d fs (Suc j)) * \<mu> fs i j" 
  let ?dmu' = "\<lambda> i j. ?r (d fs' (Suc j)) * \<mu> fs' i j" 
  note dmu = fs.d\<mu>
  note dmu' = fs'.d\<mu>
  note inv' = LLL_invD[OF inv]
  have nim1: "?n i + square_rat (\<mu> fs i (i - 1)) * ?n (i - 1) = 
    ?n' (i - 1)" by (subst swap(4), insert i, auto)
  have ni: "?n i * (?n (i - 1) / ?n' (i - 1)) = ?n' i"
    by (subst swap(4)[of i], insert i i0, auto)
  have mu': "\<mu> fs i (i - 1) * (?n (i - 1) / ?n' (i - 1)) = \<mu> fs' i (i - 1)"
    by (subst swap(5), insert i i0, auto)
  have fi: "fs ! (i - 1) = fs' ! i" "fs ! i = fs' ! (i - 1)" 
    unfolding fs'_def using inv'(6) i i0 by auto
  let ?d'i = "(d fs (Suc i) * d fs (i - 1) + d\<mu> fs i (i - 1) * d\<mu> fs i (i - 1)) div (d fs i)" 
  have rat': "ii < m \<Longrightarrow> j < ii \<Longrightarrow> ?r (d\<mu> fs' ii j) = ?dmu' ii j" for ii j 
     using dmu'[of j ii] LLL_invD[OF swap(1)] unfolding d\<mu>_def fs'.d\<mu>_def d_def fs'.d_def by auto
   have rat: "ii < m \<Longrightarrow> j < ii \<Longrightarrow> ?r (d\<mu> fs ii j) = ?dmu ii j" for ii j
     using dmu[of j ii] LLL_invD[OF inv] unfolding d\<mu>_def fs.d\<mu>_def d_def fs.d_def by auto
  from i0 i have sim1: "Suc (i - 1) = i" and im1: "i - 1 < m" by auto
  from LLL_d_Suc[OF inv im1, unfolded sim1] 
  have dn_im1: "?dn (i - 1) = ?r (d fs i) * ?r (d fs (i - 1))" by simp
  note pos = Gramian_determinant[OF inv le_refl] 
  from pos(2) have "?r (gs.Gramian_determinant fs m) \<noteq> 0" by auto
  from this[unfolded pos(1)] have nzero: "ii < m \<Longrightarrow> ?n ii \<noteq> 0" for ii by auto
  note pos = Gramian_determinant[OF swap(1) le_refl] 
  from pos(2) have "?r (gs.Gramian_determinant fs' m) \<noteq> 0" by auto
  from this[unfolded pos(1)] have nzero': "ii < m \<Longrightarrow> ?n' ii \<noteq> 0" for ii by auto
  have dzero: "ii \<le> m \<Longrightarrow> d fs ii \<noteq> 0" for ii using LLL_d_pos[OF inv, of ii] by auto
  have dzero': "ii \<le> m \<Longrightarrow> d fs' ii \<noteq> 0" for ii using LLL_d_pos[OF swap(1), of ii] by auto

  {
    define start where "start = ?dmu' i (i - 1)" 
    have "start = (?n' (i - 1) / ?n (i - 1) * ?r (d fs i)) * \<mu> fs' i (i - 1)" 
      using start_def swap(6)[of i] i i0 by simp
    also have "\<mu> fs' i (i - 1) = \<mu> fs i (i - 1) * (?n (i - 1) / ?n' (i - 1))" 
      using mu' by simp
    also have "(?n' (i - 1) / ?n (i - 1) * ?r (d fs i)) * \<dots> = ?r (d fs i) * \<mu> fs i (i - 1)" 
      using nzero[OF im1] nzero'[OF im1] by simp
    also have "\<dots> = ?dmu i (i - 1)" using i0 by simp
    finally have "?dmu' i (i - 1) = ?dmu i (i - 1)" unfolding start_def .
  } note dmu_i_im1 = this
  { (* d updates *)
    fix j
    assume j: "j \<le> m" 
    define start where "start = d fs' j" 
    {
      assume jj: "j \<noteq> i" 
      have "?r start = ?r (d fs' j)" unfolding start_def ..
      also have "?r (d fs' j) = ?r (d fs j)" 
        by (subst swap(6), insert j jj, auto)
      finally have "start = d fs j" by simp
    } note d_j = this 
    {
      assume jj: "j = i"  
      have "?r start = ?r (d fs' i)" unfolding start_def unfolding jj by simp
      also have "\<dots> = ?n' (i - 1) / ?n (i - 1) * ?r (d fs i)" 
        by (subst swap(6), insert i, auto)
      also have "?n' (i - 1) = (?r (d fs i) / ?r (d fs i)) * (?r (d fs i) / ?r (d fs i)) 
          * (?n i  + \<mu> fs i (i - 1) * \<mu> fs i (i - 1) * ?n (i - 1))" 
        by (subst swap(4)[OF im1], insert dzero[of i], insert i, simp)
      also have "?n (i - 1) = ?r (d fs i) / ?r (d fs (i - 1))" 
        unfolding LLL_d_Suc[OF inv im1, unfolded sim1] using dzero[of "i - 1"] i0 i by simp
      finally have "?r start = 
          ((?r (d fs i) * ?n i) * ?r (d fs (i - 1)) + ?dmu i (i - 1) * ?dmu i (i - 1)) 
          / (?r (d fs i))" 
        using i0 dzero[of i] i dzero[of "i - 1"]
        by (simp add: ring_distribs)
      also have "?r (d fs i) * ?n i = ?r (d fs (Suc i))" 
        unfolding LLL_d_Suc[OF inv i] by simp
      also have "?dmu i (i - 1) = ?r (d\<mu> fs i (i - 1))" by (subst rat, insert i i0, auto)
      finally have "?r start = (?r (d fs (Suc i) * d fs (i - 1) + d\<mu> fs i (i - 1) * d\<mu> fs i (i - 1)))
          / (?r (d fs i))" by simp
      from division_to_div[OF this]
      have "start = ?d'i" .
    } note d_i = this
    from d_j d_i show "d fs' j = (if j = i then ?d'i else d fs j)" unfolding start_def by auto
  } 
  have "length fs' = m" 
    using fs'_def inv'(6) by auto
  {
    fix ii j
    assume ii: "ii < m" and j: "j < ii" 
    from j ii have sj: "Suc j \<le> m" by auto
    note swaps = swap(5)[OF ii j] swap(6)[OF sj]
    show "d\<mu> fs' ii j = ?new_mu ii j" 
    proof (cases "ii < i - 1")
      case small: True
      hence id: "?new_mu ii j = d\<mu> fs ii j" by auto
      show ?thesis using swaps small ii j i i0 by (auto simp: d\<mu>_def)
    next
      case False
      from j ii have sj: "Suc j \<le> m" by auto
      let ?start = "d\<mu> fs' ii j" 
      define start where "start = ?start" 
      note rat'[OF ii j]
      note rat_ii_j = rat[OF ii j]
      from False consider (I) "ii = i" "j = i - 1" | (Is) "ii = i" "j \<noteq> i - 1" | 
          (Im1) "ii = i - 1" | (large) "ii > i" by linarith
      thus ?thesis
      proof cases
        case iii: Is
        show ?thesis unfolding swaps d\<mu>_def using iii ii i i0 by auto
      next
        case iii: I
        show ?thesis using dmu_i_im1 rat_ii_j iii i0 by (auto simp: d\<mu>_def)
      next
        case iii: Im1
        show ?thesis unfolding swaps d\<mu>_def using iii ii i j i0 by auto
      next
        case iii: large
        consider (jj) "j \<noteq> i - 1" "j \<noteq> i" | (ji) "j = i" | (jim1) "j = i - 1" by linarith
        thus ?thesis 
        proof cases
          case jj
          show ?thesis unfolding swaps d\<mu>_def using iii ii i j jj i0 by auto
        next
          case ji
          have "?r start = ?dmu' ii j" unfolding start_def by fact
          also have "?r (d fs' (Suc j)) = ?r (d fs (Suc i))" unfolding swaps unfolding ji by simp 
          also have "\<mu> fs' ii j = \<mu> fs ii (i - 1) - \<mu> fs i (i - 1) * \<mu> fs ii i" 
            unfolding swaps unfolding ji using i0 iii by auto
          also have "?r (d fs (Suc i)) * \<dots> = ?r (d fs (Suc i)) * ?r (d fs i) / ?r (d fs i) * \<dots>" 
            using dzero[of i] i by auto
          also have "\<dots> =  
            (?r (d fs (Suc i)) * ?dmu ii (i - 1) - ?dmu i (i - 1) * ?dmu ii i) / ?r (d fs i)" 
            using i0 by (simp add: field_simps)
          also have "\<dots> = 
            (?r (d fs (Suc i)) * ?r (d\<mu> fs ii (i - 1)) - ?r (d\<mu> fs i (i - 1)) * ?r (d\<mu> fs ii i)) / ?r (d fs i)" 
            by (subst (1 2 3) rat, insert i i0 ii iii, auto)
          also have "\<dots> = ?r (d fs (Suc i) * d\<mu> fs ii (i - 1) - d\<mu> fs i (i - 1) * d\<mu> fs ii i) / ?r (d fs i)" 
            (is "_ = of_int ?x / _")
            by simp
          finally have "?r start = ?r ?x / ?r (d fs i)" .
          from division_to_div[OF this]
          have id: "?start = (d fs (Suc i) * d\<mu> fs ii (i - 1) - d\<mu> fs i (i - 1) * d\<mu> fs ii j) div d fs i" 
            unfolding start_def ji .
          show ?thesis unfolding id using iii ji by simp
        next
          case jim1
          hence id'': "(j = i - 1) = True" "(j = i) = False" using i0 by auto
          have "?r (start) = ?dmu' ii j" unfolding start_def by fact
          also have "\<mu> fs' ii j = \<mu> fs ii (i - 1) * \<mu> fs' i (i - 1) +
                             \<mu> fs ii i * ?n i / ?n' (i - 1)" (is "_ = ?x1 + ?x2")
            unfolding swaps unfolding jim1 using i0 iii by auto
          also have "?r (d fs' (Suc j)) * (?x1 + ?x2)
              = ?r (d fs' (Suc j)) * ?x1 + ?r (d fs' (Suc j)) * ?x2" by (simp add: ring_distribs)
          also have "?r (d fs' (Suc j)) * ?x1 = ?dmu' i (i - 1) * (?r (d fs i) * \<mu> fs ii (i - 1))
            / ?r (d fs i)"
            unfolding jim1 using i0 dzero[of i] i by simp
          also have "?dmu' i (i - 1) = ?dmu i (i - 1)" by fact
          also have "?r (d fs i) * \<mu> fs ii (i - 1) = ?dmu ii (i - 1)" using i0 by simp
          also have "?r (d fs' (Suc j)) = ?n' (i - 1) * ?r (d fs i) / ?n (i - 1)" 
            unfolding swaps unfolding jim1 using i0 i by simp 
          also have "\<dots> * ?x2 = (?n i * ?r (d fs i)) / ?n (i - 1) * \<mu> fs ii i" 
            using i0 nzero'[of "i - 1"] i by simp
          also have "?n i * ?r (d fs i) = ?r (d fs (Suc i))" unfolding LLL_d_Suc[OF inv i] ..
          also have "?r (d fs (Suc i)) / ?n (i - 1) * \<mu> fs ii i = ?dmu ii i / ?n (i - 1)" by simp
          also have "\<dots> = ?dmu ii i * ?r (d fs (i - 1) * d fs (i - 1)) / ?dn (i - 1)" 
            using dzero[of "i - 1"] i by simp
          finally have "?r start = (?dmu i (i - 1) * ?dmu ii j * ?dn (i - 1) + 
             ?dmu ii i * (?r (d fs (i - 1) * d fs (i - 1) * d fs i))) / (?r (d fs i) * ?dn (i - 1))"
            unfolding add_divide_distrib of_int_mult jim1
            using dzero[of "i - 1"] nzero[of "i - 1"] i dzero[of i] by auto
          also have "\<dots> = (?r (d\<mu> fs i (i - 1)) * ?r (d\<mu> fs ii j) * (?r (d fs i) * ?r (d fs (i - 1))) + 
             ?r (d\<mu> fs ii i) * (?r (d fs (i - 1) * d fs (i - 1) * d fs i))) / (?r (d fs i) * (?r (d fs i) * ?r (d fs (i - 1))))" 
            unfolding dn_im1 
            by (subst (1 2 3) rat, insert i ii iii i0 j, auto)
          also have "\<dots> = (?r (d\<mu> fs i (i - 1)) * ?r (d\<mu> fs ii j) + ?r (d\<mu> fs ii i) * ?r (d fs (i - 1))) 
              / ?r (d fs i)" 
            unfolding of_int_mult using dzero[of i] dzero[of "i - 1"] i i0 by (auto simp: field_simps)
          also have "\<dots> = ?r (d\<mu> fs i (i - 1) * d\<mu> fs ii j + d\<mu> fs ii i * d fs (i - 1)) / ?r (d fs i)" 
            (is "_ = of_int ?x / _" )
            by simp
          finally have "?r start = ?r ?x / ?r (d fs i)" .
          from division_to_div[OF this]
          have id: "?start = (d\<mu> fs i (i - 1) * d\<mu> fs ii j + d\<mu> fs ii i * d fs (i - 1)) div (d fs i)" 
            unfolding start_def .
          show ?thesis unfolding id using iii jim1 i0 by auto
        qed
      qed
    qed
  }
qed

end
end