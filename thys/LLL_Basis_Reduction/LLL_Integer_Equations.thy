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
begin


context LLL
begin

lemma d_d\<mu>_add_row: assumes Linv: "LLL_invariant True i fs"
  and i: "i < m"  and j: "j < i" 
  and c: "c = round (\<mu> fs i j)" 
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

lemma d_d\<mu>_swap: assumes inv: "LLL_invariant False k fs"
  and k: "k < m"
  and k0: "k \<noteq> 0" 
  and norm_ineq: "sq_norm (gso fs (k - 1)) > \<alpha> * sq_norm (gso fs k)" 
  and fs'_def: "fs' = fs[k := fs ! (k - 1), k - 1 := fs ! k]" 
shows (* d-updates *)
  "\<And> i. i \<le> m \<Longrightarrow>
      d fs' i = (
        if i = k then 
          (d fs (Suc k) * d fs (k - 1) + d\<mu> fs k (k - 1) * d\<mu> fs k (k - 1)) div d fs k 
        else d fs i)"
and (* d\<mu>-updates *)
  "\<And> i j. i < m \<Longrightarrow> j < i \<Longrightarrow> 
      d\<mu> fs' i j = (
        if i = k - 1 then 
           d\<mu> fs k j
        else if i = k \<and> j \<noteq> k - 1 then 
             d\<mu> fs (k - 1) j
        else if i > k \<and> j = k then
           (d fs (Suc k) * d\<mu> fs i (k - 1) - d\<mu> fs k (k - 1) * d\<mu> fs i j) div d fs k
        else if i > k \<and> j = k - 1 then 
           (d\<mu> fs k (k - 1) * d\<mu> fs i j + d\<mu> fs i k * d fs (k - 1)) div d fs k
        else d\<mu> fs i j)" 
    (is "\<And> i j. _ \<Longrightarrow> _ \<Longrightarrow> _ = ?new_mu i j")
proof -
  note swap = basis_reduction_swap[OF inv k k0 norm_ineq fs'_def]
  from k k0 have kk: "k - 1 < k" and le_m: "k - 1 \<le> m" "k \<le> m" "Suc k \<le> m" by auto
  from LLL_invD[OF inv] have len: "length fs = m" by auto
  interpret fs: fs_int' n m fs_init \<alpha> False k fs
    by standard (use inv in auto)
  interpret fs': fs_int' n m fs_init \<alpha> False "k - 1" fs'
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
  have nim1: "?n k + square_rat (\<mu> fs k (k - 1)) * ?n (k - 1) = 
    ?n' (k - 1)" by (subst swap(4), insert k, auto)
  have ni: "?n k * (?n (k - 1) / ?n' (k - 1)) = ?n' k"
    by (subst swap(4)[of k], insert k k0, auto)
  have mu': "\<mu> fs k (k - 1) * (?n (k - 1) / ?n' (k - 1)) = \<mu> fs' k (k - 1)"
    by (subst swap(5), insert k k0, auto)
  have fi: "fs ! (k - 1) = fs' ! k" "fs ! k = fs' ! (k - 1)" 
    unfolding fs'_def using inv'(6) k k0 by auto
  let ?d'i = "(d fs (Suc k) * d fs (k - 1) + d\<mu> fs k (k - 1) * d\<mu> fs k (k - 1)) div (d fs k)" 
  have rat': "i < m \<Longrightarrow> j < i \<Longrightarrow> ?r (d\<mu> fs' i j) = ?dmu' i j" for i j 
     using dmu'[of j i] LLL_invD[OF swap(1)] unfolding d\<mu>_def fs'.d\<mu>_def d_def fs'.d_def by auto
   have rat: "i < m \<Longrightarrow> j < i \<Longrightarrow> ?r (d\<mu> fs i j) = ?dmu i j" for i j
     using dmu[of j i] LLL_invD[OF inv] unfolding d\<mu>_def fs.d\<mu>_def d_def fs.d_def by auto
  from k k0 have sim1: "Suc (k - 1) = k" and km1: "k - 1 < m" by auto
  from LLL_d_Suc[OF inv km1, unfolded sim1] 
  have dn_km1: "?dn (k - 1) = ?r (d fs k) * ?r (d fs (k - 1))" by simp
  note pos = Gramian_determinant[OF inv le_refl] 
  from pos(2) have "?r (gs.Gramian_determinant fs m) \<noteq> 0" by auto
  from this[unfolded pos(1)] have nzero: "i < m \<Longrightarrow> ?n i \<noteq> 0" for i by auto
  note pos = Gramian_determinant[OF swap(1) le_refl] 
  from pos(2) have "?r (gs.Gramian_determinant fs' m) \<noteq> 0" by auto
  from this[unfolded pos(1)] have nzero': "i < m \<Longrightarrow> ?n' i \<noteq> 0" for i by auto
  have dzero: "i \<le> m \<Longrightarrow> d fs i \<noteq> 0" for i using LLL_d_pos[OF inv, of i] by auto
  have dzero': "i \<le> m \<Longrightarrow> d fs' i \<noteq> 0" for i using LLL_d_pos[OF swap(1), of i] by auto

  {
    define start where "start = ?dmu' k (k - 1)" 
    have "start = (?n' (k - 1) / ?n (k - 1) * ?r (d fs k)) * \<mu> fs' k (k - 1)" 
      using start_def swap(6)[of k] k k0 by simp
    also have "\<mu> fs' k (k - 1) = \<mu> fs k (k - 1) * (?n (k - 1) / ?n' (k - 1))" 
      using mu' by simp
    also have "(?n' (k - 1) / ?n (k - 1) * ?r (d fs k)) * \<dots> = ?r (d fs k) * \<mu> fs k (k - 1)" 
      using nzero[OF km1] nzero'[OF km1] by simp
    also have "\<dots> = ?dmu k (k - 1)" using k0 by simp
    finally have "?dmu' k (k - 1) = ?dmu k (k - 1)" unfolding start_def .
  } note dmu_i_im1 = this
  { (* d updates *)
    fix j
    assume j: "j \<le> m" 
    define start where "start = d fs' j" 
    {
      assume jj: "j \<noteq> k" 
      have "?r start = ?r (d fs' j)" unfolding start_def ..
      also have "?r (d fs' j) = ?r (d fs j)" 
        by (subst swap(6), insert j jj, auto)
      finally have "start = d fs j" by simp
    } note d_j = this 
    {
      assume jj: "j = k"  
      have "?r start = ?r (d fs' k)" unfolding start_def unfolding jj by simp
      also have "\<dots> = ?n' (k - 1) / ?n (k - 1) * ?r (d fs k)" 
        by (subst swap(6), insert k, auto)
      also have "?n' (k - 1) = (?r (d fs k) / ?r (d fs k)) * (?r (d fs k) / ?r (d fs k)) 
          * (?n k  + \<mu> fs k (k - 1) * \<mu> fs k (k - 1) * ?n (k - 1))" 
        by (subst swap(4)[OF km1], insert dzero[of k], insert k, simp)
      also have "?n (k - 1) = ?r (d fs k) / ?r (d fs (k - 1))" 
        unfolding LLL_d_Suc[OF inv km1, unfolded sim1] using dzero[of "k - 1"] k k0 by simp
      finally have "?r start = 
          ((?r (d fs k) * ?n k) * ?r (d fs (k - 1)) + ?dmu k (k - 1) * ?dmu k (k - 1)) 
          / (?r (d fs k))" 
        using k k0 dzero[of k] dzero[of "k - 1"]
        by (simp add: ring_distribs)
      also have "?r (d fs k) * ?n k = ?r (d fs (Suc k))" 
        unfolding LLL_d_Suc[OF inv k] by simp
      also have "?dmu k (k - 1) = ?r (d\<mu> fs k (k - 1))" by (subst rat, insert k k0, auto)
      finally have "?r start = (?r (d fs (Suc k) * d fs (k - 1) + d\<mu> fs k (k - 1) * d\<mu> fs k (k - 1)))
          / (?r (d fs k))" by simp
      from division_to_div[OF this]
      have "start = ?d'i" .
    } note d_i = this
    from d_j d_i show "d fs' j = (if j = k then ?d'i else d fs j)" unfolding start_def by auto
  } 
  have "length fs' = m" 
    using fs'_def inv'(6) by auto
  {
    fix i j
    assume i: "i < m" and j: "j < i" 
    from j i have sj: "Suc j \<le> m" by auto
    note swaps = swap(5)[OF i j] swap(6)[OF sj]
    show "d\<mu> fs' i j = ?new_mu i j" 
    proof (cases "i < k - 1")
      case small: True
      hence id: "?new_mu i j = d\<mu> fs i j" by auto
      show ?thesis using swaps small i j k k0 by (auto simp: d\<mu>_def)
    next
      case False
      from j i have sj: "Suc j \<le> m" by auto
      let ?start = "d\<mu> fs' i j" 
      define start where "start = ?start" 
      note rat'[OF i j]
      note rat_i_j = rat[OF i j]
      from False consider (i_k) "i = k" "j = k - 1" | (i_small) "i = k" "j \<noteq> k - 1" | 
          (i_km1) "i = k - 1" | (i_large) "i > k" by linarith
      thus ?thesis
      proof cases
        case *: i_small
        show ?thesis unfolding swaps d\<mu>_def using * i k k0 by auto
      next
        case *: i_k
        show ?thesis using dmu_i_im1 rat_i_j * k0 by (auto simp: d\<mu>_def)
      next
        case *: i_km1
        show ?thesis unfolding swaps d\<mu>_def using * i j k k0 by auto
      next
        case *: i_large
        consider (jj) "j \<noteq> k - 1" "j \<noteq> k" | (ji) "j = k" | (jim1) "j = k - 1" by linarith
        thus ?thesis 
        proof cases
          case jj
          show ?thesis unfolding swaps d\<mu>_def using * i j jj k k0 by auto
        next
          case ji
          have "?r start = ?dmu' i j" unfolding start_def by fact
          also have "?r (d fs' (Suc j)) = ?r (d fs (Suc k))" unfolding swaps unfolding ji by simp 
          also have "\<mu> fs' i j = \<mu> fs i (k - 1) - \<mu> fs k (k - 1) * \<mu> fs i k" 
            unfolding swaps unfolding ji using k0 * by auto
          also have "?r (d fs (Suc k)) * \<dots> = ?r (d fs (Suc k)) * ?r (d fs k) / ?r (d fs k) * \<dots>" 
            using dzero[of k] k by auto
          also have "\<dots> =  
            (?r (d fs (Suc k)) * ?dmu i (k - 1) - ?dmu k (k - 1) * ?dmu i k) / ?r (d fs k)" 
            using k0 by (simp add: field_simps)
          also have "\<dots> = 
            (?r (d fs (Suc k)) * ?r (d\<mu> fs i (k - 1)) - ?r (d\<mu> fs k (k - 1)) * ?r (d\<mu> fs i k)) / ?r (d fs k)" 
            by (subst (1 2 3) rat, insert k k0 i *, auto)
          also have "\<dots> = ?r (d fs (Suc k) * d\<mu> fs i (k - 1) - d\<mu> fs k (k - 1) * d\<mu> fs i k) / ?r (d fs k)" 
            (is "_ = of_int ?x / _")
            by simp
          finally have "?r start = ?r ?x / ?r (d fs k)" .
          from division_to_div[OF this]
          have id: "?start = (d fs (Suc k) * d\<mu> fs i (k - 1) - d\<mu> fs k (k - 1) * d\<mu> fs i j) div d fs k" 
            unfolding start_def ji .
          show ?thesis unfolding id using * ji by simp
        next
          case jim1
          hence id'': "(j = k - 1) = True" "(j = k) = False" using k0 by auto
          have "?r (start) = ?dmu' i j" unfolding start_def by fact
          also have "\<mu> fs' i j = \<mu> fs i (k - 1) * \<mu> fs' k (k - 1) +
                             \<mu> fs i k * ?n k / ?n' (k - 1)" (is "_ = ?x1 + ?x2")
            unfolding swaps unfolding jim1 using k0 * by auto
          also have "?r (d fs' (Suc j)) * (?x1 + ?x2)
              = ?r (d fs' (Suc j)) * ?x1 + ?r (d fs' (Suc j)) * ?x2" by (simp add: ring_distribs)
          also have "?r (d fs' (Suc j)) * ?x1 = ?dmu' k (k - 1) * (?r (d fs k) * \<mu> fs i (k - 1))
            / ?r (d fs k)"
            unfolding jim1 using k0 dzero[of k] k by simp
          also have "?dmu' k (k - 1) = ?dmu k (k - 1)" by fact
          also have "?r (d fs k) * \<mu> fs i (k - 1) = ?dmu i (k - 1)" using k0 by simp
          also have "?r (d fs' (Suc j)) = ?n' (k - 1) * ?r (d fs k) / ?n (k - 1)" 
            unfolding swaps unfolding jim1 using k k0 by simp 
          also have "\<dots> * ?x2 = (?n k * ?r (d fs k)) / ?n (k - 1) * \<mu> fs i k" 
            using k k0 nzero'[of "k - 1"] by simp
          also have "?n k * ?r (d fs k) = ?r (d fs (Suc k))" unfolding LLL_d_Suc[OF inv k] ..
          also have "?r (d fs (Suc k)) / ?n (k - 1) * \<mu> fs i k = ?dmu i k / ?n (k - 1)" by simp
          also have "\<dots> = ?dmu i k * ?r (d fs (k - 1) * d fs (k - 1)) / ?dn (k - 1)" 
            using dzero[of "k - 1"] k by simp
          finally have "?r start = (?dmu k (k - 1) * ?dmu i j * ?dn (k - 1) + 
             ?dmu i k * (?r (d fs (k - 1) * d fs (k - 1) * d fs k))) / (?r (d fs k) * ?dn (k - 1))"
            unfolding add_divide_distrib of_int_mult jim1
            using dzero[of "k - 1"] nzero[of "k - 1"] k dzero[of k] by auto
          also have "\<dots> = (?r (d\<mu> fs k (k - 1)) * ?r (d\<mu> fs i j) * (?r (d fs k) * ?r (d fs (k - 1))) + 
             ?r (d\<mu> fs i k) * (?r (d fs (k - 1) * d fs (k - 1) * d fs k))) / (?r (d fs k) * (?r (d fs k) * ?r (d fs (k - 1))))" 
            unfolding dn_km1 
            by (subst (1 2 3) rat, insert k k0 i * j, auto)
          also have "\<dots> = (?r (d\<mu> fs k (k - 1)) * ?r (d\<mu> fs i j) + ?r (d\<mu> fs i k) * ?r (d fs (k - 1))) 
              / ?r (d fs k)" 
            unfolding of_int_mult using dzero[of k] dzero[of "k - 1"] k k0 by (auto simp: field_simps)
          also have "\<dots> = ?r (d\<mu> fs k (k - 1) * d\<mu> fs i j + d\<mu> fs i k * d fs (k - 1)) / ?r (d fs k)" 
            (is "_ = of_int ?x / _" )
            by simp
          finally have "?r start = ?r ?x / ?r (d fs k)" .
          from division_to_div[OF this]
          have id: "?start = (d\<mu> fs k (k - 1) * d\<mu> fs i j + d\<mu> fs i k * d fs (k - 1)) div (d fs k)" 
            unfolding start_def .
          show ?thesis unfolding id using * jim1 k0 by auto
        qed
      qed
    qed
  }
qed

end
end