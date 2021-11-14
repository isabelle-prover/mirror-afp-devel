subsection \<open>Application: Compute \<open>n\<close>-th Roots of Complex Numbers\<close>

text \<open>We provide a more efficient algorithm to compute \<open>n\<close>-th roots of complex numbers
  than the existing implementation.\<close>

theory Complex_Roots_IA_Code
  imports 
    Cubic_Quartic_Equations.Complex_Roots
    Roots_via_IA
begin

text \<open>TODO: One might change @{const complex_roots_of_int_poly} to @{const complex_roots_of_int_poly3}
  in order to avoid an unnecessary factorization of an integer polynomial. However, then
  this change already needs to be performed within the definition of @{const all_croots}.\<close> 
lift_definition all_croots_part1 :: "nat \<Rightarrow> complex \<Rightarrow> complex genuine_roots_aux" is
  "\<lambda> n x. if n = 0 \<or> x = 0 \<or> \<not> algebraic x then (1,[],0, filter_fun_complex 1) 
         else let p = min_int_poly x;
              q = poly_nth_root n p;
              zeros = complex_roots_of_int_poly q;
              r = Polynomial.monom 1 n - [:x:]
         in (r,zeros, n, filter_fun_complex r)"
  subgoal for n x
  proof (cases "n = 0 \<or> x = 0 \<or> \<not> algebraic x")
    case True
    thus ?thesis by (simp add: filter_fun_complex)
  next
    case False
    hence *: "algebraic x" "n \<noteq> 0" "x \<noteq> 0" by auto
    {
      fix z
      assume zn: "z^n = x" 
      from *(1) have repr: "min_int_poly x represents x" by auto
      from represents_nth_root[OF *(2) zn repr]
      have "poly_nth_root n (min_int_poly x) represents z" .
    }
    moreover have "card {z. z ^ n = x} = n"
      by (rule card_nth_roots) (use * in auto)
    ultimately show ?thesis using * 
      by (auto simp: Let_def complex_roots_of_int_poly filter_fun_complex poly_monom)
  qed
  done

declare all_croots_code[code del]

lemma all_croots_improved_code[code]: 
  "all_croots n x = (if n = 0 then [] else if x = 0 then [0]
     else if algebraic x then genuine_roots_impl (all_croots_part1 n x)
     else Code.abort (STR ''all_croots invoked on non-algebraic number'') (\<lambda> _. all_croots n x))"
proof (cases "n = 0")
  case True
  thus ?thesis unfolding all_croots_def by simp
next
  case n: False
  show ?thesis
  proof (cases "x = 0")
    case x: False
    show ?thesis
    proof (cases "algebraic x")
      case False
      with n x show ?thesis by simp
    next
      case True
      define t where "t = ?thesis" 
      have "t \<longleftrightarrow> filter (\<lambda>y. y ^ n = x)
                (complex_roots_of_int_poly (poly_nth_root n (min_int_poly x)))
            = genuine_roots_impl (all_croots_part1 n x)" 
        unfolding t_def
        by (subst all_croots_code[of n x], unfold Let_def, insert n x True, auto)
      also have "\<dots>" using n x True unfolding genuine_roots_impl_def
        by (transfer, simp add: Let_def genuine_roots_def poly_monom)
      finally show ?thesis unfolding t_def by simp
    qed
  next
    case x: True
    have "set (all_croots n 0) = {0}" unfolding all_croots[OF n] using n by simp
    moreover have "distinct (all_croots n 0)" unfolding all_croots_def using n
      by (auto intro!: distinct_filter complex_roots_of_int_poly)
    ultimately have "all_croots n 0 = [0]"
      by (smt (verit, del_insts) distinct.simps(2) distinct_singleton insert_ident list.set_cases list.set_intros(1) list.simps(15) mem_Collect_eq set_empty singleton_conv)
    moreover have "?thesis \<longleftrightarrow> all_croots n 0 = [0]" using n x by simp
    ultimately show ?thesis by auto
  qed
qed

end
