(*
Title: Butterfly Algorithm for Number Theoretic Transform
Author: Thomas Ammer
*)

theory Butterfly
  imports NTT "HOL-Library.Discrete"
begin

text \<open>\pagebreak\<close>

section \<open>Butterfly Algorithms\<close>
text \<open>\label{Butterfly}\<close>

text \<open>\indent Several recursive algorithms for $FFT$ based on 
the divide and conquer principle have been developed in order to speed up the transform.
A method for reducing complexity is the butterfly scheme. 
In this formalization, we consider the butterfly algorithm by Cooley 
and Tukey~\parencite{Good1997} adapted to the setting of \textit{NTT}.
\<close>

text \<open>\noindent We additionally assume that $n$ is power of two.\<close>

locale butterfly = ntt +
  fixes N
  assumes n_two_pot: "n = 2^N"
begin

subsection \<open>Recursive Definition\<close>

text \<open>Let's recall the definition of a transformed vector element:
\begin{equation*}
\mathsf{NTT}(\vec{x})_i = \sum _{j = 0} ^{n-1} x_j \cdot \omega ^{i\cdot j} 
\end{equation*}

We assume $n = 2^N$ and obtain:

\begin{align*}
\sum _{j = 0} ^{< 2^N} x_j \cdot \omega ^{i\cdot j} \\ &= 
\sum _{j = 0} ^{< 2^{N-1}} x_{2j} \cdot \omega ^{i\cdot 2j} +
 \sum _{j = 0} ^{< 2^{N-1}} x_{2j+1} \cdot \omega ^{i\cdot (2j+1)} \\
& = \sum _{j = 0} ^{< 2^{N-1}} x_{2j} \cdot (\omega^2) ^{i\cdot j} +
 \omega^i \cdot \sum _{j = 0} ^{< 2^{N-1}} x_{2j+1} \cdot (\omega^2) ^{i\cdot j}\\
& = (\sum _{j = 0} ^{< 2^{N-2}} x_{4j} \cdot (\omega^4) ^{i\cdot j}  +
 \omega^i \cdot \sum _{j = 0} ^{< 2^{N-2}} x_{4j+2} \cdot (\omega^4) ^{i\cdot j}) \\
& \hspace{1cm}+ \omega^i \cdot (\sum _{j = 0} ^{< 2^{N-2}} x_{4j+1} \cdot (\omega^4) ^{i\cdot j}  +
 \omega^i \cdot \sum _{j = 0} ^{< 2^{N-2}} x_{4j+3} \cdot (\omega^4) ^{i\cdot j}) \text{ etc.}
\end{align*}

which gives us a recursive algorithm:

\begin{itemize}
\item Compose vectors consisting of elements at even and odd indices respectively
\item Compute a transformation of these vectors recursively where the dimensions are halved.
\item Add results after scaling the second subresult by $\omega^i$
\end{itemize}

\<close>

text \<open>Now we give a functional definition of the analogue to $FFT$ adapted to finite fields. 
A gentle introduction to $FFT$ can be found in~\parencite{10.5555/1614191}. 
For the fast implementation of Number Theoretic Transform in particular, have a look at~\parencite{cryptoeprint:2016/504}.\<close>

text \<open>(The following lemma is needed to obtain an automated termination proof of $FNTT$.)\<close>
lemma FNTT_termination_aux [simp]: "length (filter P [0..<l]) < Suc l"
  by (metis diff_zero le_imp_less_Suc length_filter_le length_upt)

text \<open>Please note that we closely adhere to the textbook definition which just 
talks about elements at even and odd indices. We model the informal definition by predefined functions, 
since this seems to be more handy during proofs. 
An algorithm splitting the elements smartly will be presented afterwards.\<close>

fun FNTT::"('a mod_ring) list \<Rightarrow> ('a mod_ring) list" where
"FNTT [] = []"|
"FNTT [a] = [a]"|
"FNTT nums = (let nn = length nums;
                  nums1 = [nums!i.  i \<leftarrow> filter even [0..<nn]];
                  nums2 = [nums!i.  i \<leftarrow> filter odd [0..<nn]];
                  fntt1 = FNTT nums1;
                  fntt2 = FNTT nums2;
                  sum1 = map2 (+) fntt1 (map2 ( \<lambda> x k.  x*(\<omega>^( (n div nn) * k))) fntt2 [0..<(nn div 2)]);
                  sum2 = map2 (-) fntt1 (map2 ( \<lambda> x k.  x*(\<omega>^( (n div nn) * k))) fntt2 [0..<(nn div 2)])
                   in sum1@sum2)"

lemmas [simp del] = FNTT_termination_aux


text \<open>
Finally, we want to prove correctness, i.e. $FNTT\; xs = NTT\;xs$. 
Since we consider a recursive algorithm, some kind of induction is appropriate:
Assume the claim for $\frac{2^d}{2} = 2^{d-1}$ and prove it for $2^d$, where $2^d$ is the vector length. 
This implies that we have to talk about \textit{NTT}s with respect to some powers of $\omega$.
In particular, we decide to annotate \textit{NTT} with a degree $degr$ 
indicating the referred vector length. There is a correspondence to the current level $l$ of recursion:

\begin{equation*}
degr = 2^{N-l}
\end{equation*}

\<close>

text \<open>\noindent A generalized version of \textit{NTT} keeps track of all levels during recursion:\<close>

definition "ntt_gen numbers degr i = (\<Sum>j=0..<(length numbers). (numbers ! j) * \<omega>^((n div degr)*i*j)) "

definition "NTT_gen degr numbers = map (ntt_gen numbers (degr)) [0..< length numbers]"

text \<open>Whenever generalized \textit{NTT} is applied to a list of full length,
 then its actually equal to the defined \textit{NTT}.\<close>

lemma NTT_gen_NTT_full_length: 
  assumes "length numbers =n"
  shows "NTT_gen n numbers = NTT numbers"
  unfolding NTT_gen_def ntt_gen_def NTT_def ntt_def 
  using assms by simp

subsection \<open>Arguments on Correctness\<close>
text \<open>First some general lemmas on list operations.\<close>

lemma length_even_filter: "length [f i .  i <- (filter even [0..<l])] = l-l div 2"
  by(induction l) auto

lemma length_odd_filter: "length [f i .  i <- (filter odd [0..<l])] = l div 2"
  by(induction l) auto

lemma map2_length: "length (map2 f xs ys) =  min (length xs) (length ys)"
  by (induction xs arbitrary: ys) auto

lemma map2_index: "i < length xs \<Longrightarrow> i < length ys \<Longrightarrow> (map2 f xs ys) ! i = f (xs ! i) (ys ! i)"
  by (induction xs arbitrary: ys i) auto

lemma filter_last_not: "\<not> P x \<Longrightarrow> filter P (xs@[x]) = filter P xs"
  by simp

lemma filter_even_map: "filter even [0..<2*(x::nat)] = map ((*) (2::nat)) [0..<x]"
  by(induction x) simp+

lemma filter_even_nth: "2*j < l \<Longrightarrow> 2*x = l \<Longrightarrow> (filter even [0..<l] ! j) = (2*j)"
  using filter_even_map[of x] nth_map[of j "filter even [0..<l]" "(*) 2"] by auto

lemma filter_odd_map: "filter odd [0..<2*(x::nat)] = map (\<lambda> y. (2::nat)*y +1) [0..<x]"
  by(induction x) simp+

lemma filter_odd_nth: "2*j < l \<Longrightarrow> 2*x = l \<Longrightarrow> (filter odd [0..<l] ! j) = (2*j+1)"
  using filter_odd_map[of x] nth_map[of j "filter even [0..<l]" "(*) 2"] by auto

text \<open>\noindent Lemmas by using the assumption $n = 2^N$.\<close>

text \<open>\noindent ($-1$ denotes the additive inverse of $1$ in the finite field.)\<close>

lemma n_min1_2: "n = 2  \<Longrightarrow> \<omega>  = -1" 
  using omega_properties(1) omega_properties(2) power2_eq_1_iff by blast

lemma n_min1_gr2:
  assumes "n > 2"
  shows "\<omega>^(n div 2) = -1"
proof-
  have "\<omega>^(n div 2) \<noteq> -1 \<Longrightarrow> False"
  proof-
  assume "\<omega>^(n div 2) \<noteq> -1"
  hence False
  proof (cases \<open>\<omega> ^ (n div 2) = 1\<close>)
    case True
    then show ?thesis using omega_properties(3) assms
      by auto
  next
    case False
    hence "(\<omega>^(n div 2)) ^ (2::nat) \<noteq> 1" 
      by (smt (verit, ccfv_threshold) n_two_pot One_nat_def \<open>\<omega> ^ (n div 2) \<noteq> - 1\<close> diff_zero leD n_lst2 not_less_eq omega_properties(1) one_less_numeral_iff one_power2 power2_eq_square power_mult power_one_right power_strict_increasing_iff semiring_norm(76) square_eq_iff two_powr_div two_powrs_div)
    moreover have "(n div 2) * 2  = n" using n_two_pot n_lst2  
      by (metis One_nat_def Suc_lessD assms div_by_Suc_0 one_less_numeral_iff power_0 power_one_right power_strict_increasing_iff semiring_norm(76) two_powrs_div)
    ultimately show ?thesis  using omega_properties(1)
      by (metis power_mult)
  qed
    thus False by simp
  qed
  then show ?thesis by auto
qed

lemma div_exp_sub: "2^l  < n \<Longrightarrow> n div (2^l) = 2^(N-l)"using n_two_pot
    by (smt (z3) One_nat_def diff_is_0_eq diff_le_diff_pow div_if div_le_dividend eq_imp_le le_0_eq le_Suc_eq n_lst2 nat_less_le not_less_eq_eq numeral_2_eq_2 power_0 two_powr_div) 

lemma omega_div_exp_min1:
  assumes "2^(Suc l) \<le> n"
  shows "(\<omega> ^(n div 2^(Suc l)))^(2^l) = -1" 
proof-
  have "(\<omega> ^(n div 2^(Suc l)))^(2^l) = \<omega> ^((n div 2^(Suc l))*2^l)"
    by (simp add: power_mult)
  moreover have "(n div 2^(Suc l)) = 2^(N - Suc l)" using assms div_exp_sub 
    by (metis n_two_pot eq_imp_le le_neq_implies_less one_less_numeral_iff power_diff power_inject_exp semiring_norm(76) zero_neq_numeral)
  moreover have "N \<ge> Suc l" using assms n_two_pot 
    by (metis diff_is_0_eq diff_le_diff_pow gr0I leD le_refl)
  moreover hence "(2::nat)^(N - Suc l)*2^l = 2^(N- 1)" 
    by (metis Nat.add_diff_assoc diff_Suc_1 diff_diff_cancel diff_le_self le_add1 le_add_diff_inverse plus_1_eq_Suc power_add) 
  ultimately show ?thesis 
    by (metis n_two_pot One_nat_def \<open>n div 2 ^ Suc l = 2 ^ (N - Suc l)\<close> diff_Suc_1 div_exp_sub n_lst2 n_min1_2 n_min1_gr2 nat_less_le nat_power_eq_Suc_0_iff one_less_numeral_iff power_inject_exp power_one_right semiring_norm(76))
qed

lemma omg_n_2_min1:  "\<omega>^(n div 2) = -1" 
  by (metis n_lst2 n_min1_2 n_min1_gr2 nat_less_le numeral_Bit0_div_2 numerals(1) power_one_right)

lemma neg_cong: "-(x::('a mod_ring)) = - y \<Longrightarrow> x = y" by simp

text \<open>Generalized \textit{NTT} indeed describes all recursive levels, 
and thus, it is actually equivalent to the ordinary \textit{NTT} definition.\<close>

theorem FNTT_NTT_gen_eq: "length numbers = 2^l \<Longrightarrow> 2^l \<le> n \<Longrightarrow> FNTT numbers = NTT_gen (length numbers) numbers"
proof(induction l arbitrary: numbers)
  case 0
  then show ?case unfolding NTT_gen_def ntt_gen_def 
    by (auto simp: length_Suc_conv)
next
  case (Suc l)
  text \<open>We define some lists that are used during the recursive call.\<close>
  define numbers1 where "numbers1 = [numbers!i .  i <- (filter even [0..<length numbers])]" 
  define numbers2 where "numbers2 = [numbers!i .  i <- (filter odd [0..<length numbers])]" 
  define fntt1 where "fntt1 = FNTT numbers1"
  define fntt2 where "fntt2 = FNTT numbers2" 
  define sum1 where 
    "sum1 = map2 (+) fntt1 (map2 ( \<lambda> x k.  x*(\<omega>^( (n div (length numbers)) * k))) 
                   fntt2 [0..<((length numbers) div 2)])" 
  define sum2 where  
    "sum2 = map2 (-) fntt1 (map2 ( \<lambda> x k.  x*(\<omega>^( (n div (length numbers)) * k))) 
                   fntt2 [0..<((length numbers) div 2)])" 
  define l1 where "l1 = length numbers1"
  define l2 where "l2 = length numbers2"
  define llen where "llen = length numbers"

  text \<open>Properties of those lists.\<close>
  have numbers1_even: "length numbers1 = 2^l" 
     using numbers1_def length_even_filter Suc by simp
   have numbers2_even: "length numbers2 = 2^l"
     using numbers2_def length_odd_filter Suc by simp
  have numbers1_fntt: "fntt1 = NTT_gen (2^l) numbers1" 
    using fntt1_def Suc.IH[of numbers1] numbers1_even Suc(3) by simp
  hence fntt1_by_index: "fntt1 ! i = ntt_gen numbers1 (2^l) i" if "i < 2^l" for i
    unfolding NTT_gen_def by (simp add: numbers1_even that)
  have numbers2_fntt: "fntt2 = NTT_gen (2^l) numbers2" 
    using fntt2_def Suc.IH[of numbers2] numbers2_even Suc(3) by simp
  hence fntt2_by_index: "fntt2 ! i = ntt_gen numbers2 (2^l) i" if "i < 2^l" for i
    unfolding NTT_gen_def
    by (simp add: numbers2_even that)
  have fntt1_length: "length fntt1 = 2^l" unfolding numbers1_fntt NTT_gen_def numbers1_def
    using numbers1_def numbers1_even by force
   have fntt2_length: "length fntt2 = 2^l" unfolding numbers2_fntt NTT_gen_def numbers2_def
     using numbers2_def numbers2_even by force

   text \<open>We show that the list resulting from $FNTT$ is equal to the $NTT$ list.
         First, we prove $FNTT$ and $NTT$ to be equal concerning their first halves.\<close>
   have before_half: "map (ntt_gen numbers llen) [0..<(llen div 2)] = sum1"
   proof-
 
     text \<open>Length is important, since we want to use list lemmas later on.\<close>
     have 00:"length (map (ntt_gen numbers llen) [0..<(llen div 2)]) =  length sum1"
       unfolding sum1_def llen_def
       using Suc(2) map2_length[of _ fntt2 "[0..<length numbers div 2]"]
       map2_length[of "(+)" fntt1 "(map2 (\<lambda>x y. x * \<omega> ^ (n div length numbers * y)) fntt2 [0..<length numbers div 2])"]
       fntt1_length fntt2_length by (simp add: mult_2)
     have 01:"length sum1 = 2^l" unfolding sum1_def 
       using "00" Suc.prems(1) sum1_def unfolding llen_def by auto

     text \<open>We show equality by extensionality w.r.t. indices.\<close>
     have 02:"(map (ntt_gen numbers llen) [0..<(llen div 2)]) ! i = sum1 ! i" 
       if "i < 2^l" for i
     proof-
       text \<open>First simplify this term.\<close>
       have 000:"(map (ntt_gen numbers llen) [0..<(llen div 2)]) ! i =
                   ntt_gen numbers llen i" 
         using "00" "01" that by auto

       text \<open>Expand the definition of $sum1$ and massage the result.\<close>
       moreover have 001:"sum1 ! i = (fntt1!i) + (fntt2!i) * (\<omega>^((n div llen) * i))"
         unfolding sum1_def using map2_index
         "00" "01" NTT_gen_def add.left_neutral diff_zero fntt1_length length_map length_upt map2_map_map map_nth nth_upt numbers2_even numbers2_fntt that llen_def by force
       moreover have 002:"(fntt1!i) = (\<Sum>j=0..<l1. (numbers1 ! j) * \<omega>^((n div (2^l))*i*j))"
         unfolding l1_def
         using fntt1_by_index[of i] that unfolding ntt_gen_def by simp
       have 003:"... = (\<Sum>j=0..<l1. (numbers ! (2*j)) * \<omega>^((n div llen)*i*(2*j)))"
         apply (rule sum_rules(2))
         subgoal for j unfolding numbers1_def 
           apply(subst llen_def[symmetric])
         proof-
           assume ass: "j < l1 "
           hence "map ((!) numbers) (filter even [0..<length numbers]) ! j = numbers ! (filter even [0..<length numbers] ! j)"
             using  nth_map[of j "filter even [0..<length numbers]" "(!) numbers" ] 
             unfolding l1_def numbers1_def
             by (metis length_map)
           moreover have "filter even [0..<llen] ! j = 2 * j" using
            filter_even_nth[of j "llen" "2^l"] Suc(2)  ass numbers1_def numbers1_even 
             unfolding llen_def l1_def by fastforce
           moreover have "n div llen * (2 * j) = ((n div (2 ^ l))  * j)"
             using Suc(2) two_powrs_div[of l N] n_two_pot two_powr_div Suc(3) llen_def
             by (metis One_nat_def div_if mult.assoc nat_less_le not_less_eq numeral_2_eq_2 power_eq_0_iff power_inject_exp zero_neq_numeral)
           ultimately show "map ((!) numbers) (filter even [0..<llen]) ! j * \<omega> ^ (n div 2 ^ l * i * j) =
                   numbers ! (2 * j) * \<omega> ^ (n div llen * i * (2 * j))" 
             unfolding llen_def l1_def l2_def by (metis (mono_tags, lifting) mult.assoc mult.left_commute)
         qed
         done
       moreover have 004:
          "(fntt2!i) * (\<omega>^((n div llen) * i)) = 
               (\<Sum>j=0..<l2.(numbers2 ! j) * \<omega>^((n div (2^l))*i*j+ (n div llen) * i))"
            apply(rule trans[where s = "(\<Sum>j = 0..<l2. numbers2 ! j * \<omega> ^ (n div 2 ^ l * i * j) * \<omega> ^ (n div llen * i))"])
         subgoal 
            unfolding l2_def llen_def
            using fntt2_by_index[of i] that sum_in[of _ "(\<omega>^((n div llen) * i))" "l2"] comm_semiring_1_class.semiring_normalization_rules(26)[of \<omega>]
            unfolding ntt_gen_def
            using sum_rules  apply presburger
            done
          apply (rule sum_rules(2))
          subgoal for j
            using fntt2_by_index[of i] that sum_in[of _ "(\<omega>^((n div llen) * i))" "l2"] comm_semiring_1_class.semiring_normalization_rules(26)[of \<omega>]
            unfolding ntt_gen_def
            apply auto
            done
          done
     have 005: "\<dots> = (\<Sum>j=0..<l2. (numbers ! (2*j+1) * \<omega>^((n div llen)*i*(2*j+1))))"
      apply (rule sum_rules(2))
       subgoal for j unfolding numbers2_def 
         apply(subst llen_def[symmetric])
           proof-
           assume ass: "j < l2 "
           hence "map ((!) numbers) (filter odd [0..<llen]) ! j = numbers ! (filter odd [0..<llen] ! j)"
             using  nth_map unfolding l2_def numbers2_def llen_def by (metis length_map)
           moreover have "filter odd [0..<llen] ! j = 2 * j +1" using
            filter_odd_nth[of j "length numbers" "2^l"] Suc(2)  ass numbers2_def numbers2_even
             unfolding l2_def numbers2_def llen_def by fastforce
           moreover have "n div llen * (2 * j) = ((n div (2 ^ l))  * j)"
             using Suc(2) two_powrs_div[of l N] n_two_pot two_powr_div Suc(3) llen_def
             by (metis One_nat_def div_if mult.assoc nat_less_le not_less_eq numeral_2_eq_2 power_eq_0_iff power_inject_exp zero_neq_numeral)
           ultimately show 
            " map ((!) numbers) (filter odd [0..<llen]) ! j * \<omega> ^ (n div 2 ^ l * i * j + n div llen * i) 
                = numbers ! (2 * j + 1) * \<omega> ^ (n div llen * i * (2 * j + 1))" unfolding llen_def
             by (smt (z3) Groups.mult_ac(2) distrib_left mult.right_neutral mult_2 mult_cancel_left)
         qed
         done
       then show ?thesis 
         using 000 001 002 003 004 005 
         unfolding sum1_def llen_def l1_def l2_def
         using sum_splice_other_way_round[of "\<lambda> d.  numbers ! d  * \<omega> ^ (n div length numbers * i * d)" "2^l"] Suc(2)
         unfolding ntt_gen_def 
         by (smt (z3) Groups.mult_ac(2) numbers1_even numbers2_even power_Suc2)
     qed
     then show ?thesis 
       by  (metis "00" "01" nth_equalityI)
   qed

   text \<open>We show equality for the indices in the second halves.\<close>
   have after_half: "map (ntt_gen numbers llen) [(llen div 2)..<llen] = sum2"
   proof-
     have 00:"length (map (ntt_gen numbers llen) [(llen div 2)..<llen]) =  length sum2"
       unfolding sum2_def llen_def 
       using Suc(2) map2_length map2_length fntt1_length fntt2_length by (simp add: mult_2)
     have 01:"length sum2 = 2^l" unfolding sum1_def 
       using "00" Suc.prems(1) sum1_def llen_def  by auto
     text \<open>Equality for every index.\<close>
     have 02:"(map (ntt_gen numbers llen)  [(llen div 2)..<llen]) ! i = sum2 ! i" 
       if "i < 2^l" for i
     proof-
       have 000:"(map (ntt_gen numbers llen)  [(llen div 2)..<llen]) ! i =  ntt_gen numbers llen (2^l+i)"
         unfolding llen_def by (simp add: Suc.prems(1) that)
       have 001:" (map2 (\<lambda>x y. x * \<omega> ^ (n div llen * y)) fntt2 [0..<llen div 2]) ! i =
                  fntt2 ! i * \<omega> ^ (n div llen * i)"
         using  Suc(2) that by (simp add:  fntt2_length  llen_def)
       have 003: "- fntt2 ! i * \<omega> ^ (n div llen * i) = 
                    fntt2 ! i * \<omega> ^ (n div llen * (i+ llen div 2))" 
         using Suc(2) omega_div_exp_min1[of l] unfolding llen_def
         by (smt (z3) Suc.prems(2) mult.commute mult.left_commute mult_1s_ring_1(2) neq0_conv nonzero_mult_div_cancel_left numeral_One pos2 power_Suc power_add power_mult)
       hence 004:"sum2 ! i = (fntt1!i) - (fntt2!i) * (\<omega>^((n div llen) * i))"
         unfolding sum2_def llen_def 
         by (simp add: Suc.prems(1) fntt1_length fntt2_length that)
       have 005:"(fntt1!i) = 
                     (\<Sum>j=0..<l1. (numbers1 ! j) * \<omega>^((n div (2^l))*i*j))"
        using fntt1_by_index that unfolding ntt_gen_def l1_def by simp
      have 006:"\<dots> =(\<Sum>j=0..<l1. (numbers ! (2*j)) * \<omega>^((n div llen)*i*(2*j)))"
         apply (rule sum_rules(2))
        subgoal for j unfolding numbers1_def 
          apply(subst llen_def[symmetric])
         proof-
           assume ass: "j < l1 "
           hence "map ((!) numbers) (filter even [0..<llen]) ! j = numbers ! (filter even [0..<llen] ! j)"
             using  nth_map unfolding llen_def l1_def numbers1_def by (metis length_map)
           moreover have "filter even [0..<llen] ! j = 2 * j" using
            filter_even_nth Suc(2)  ass numbers1_def numbers1_even llen_def l1_def by fastforce
           moreover have "n div llen * (2 * j) = ((n div (2 ^ l))  * j)"
             using Suc(2) two_powrs_div[of l N] n_two_pot two_powr_div Suc(3) llen_def
             by (metis One_nat_def div_if mult.assoc nat_less_le not_less_eq numeral_2_eq_2 power_eq_0_iff power_inject_exp zero_neq_numeral)
           ultimately show 
              "map ((!) numbers) (filter even [0..<llen]) ! j * \<omega> ^ (n div 2 ^ l * i * j) =
                        numbers ! (2 * j) * \<omega> ^ (n div llen * i * (2 * j))" 
             by (metis (mono_tags, lifting) mult.assoc mult.left_commute)
         qed
         done
        have 007:"\<dots> = (\<Sum>j=0..<l1. (numbers ! (2*j)) * \<omega>^((n div llen)*(2^l + i)*(2*j))) "
         apply (rule sum_rules(2))
         subgoal for j 
           using Suc(2) Suc(3) omega_div_exp_min1[of l] llen_def l1_def numbers1_def
           apply(smt (verit, del_insts) add.commute minus_power_mult_self mult_2 mult_minus1_right power_add power_mult)
           done
         done
       moreover have 008: "(fntt2!i) * (\<omega>^((n div llen) * i)) =
                      (\<Sum>j=0..<l2. (numbers2 ! j) * \<omega>^((n div (2^l))*i*j+ (n div llen) * i))" 
         apply(rule trans[where s = "(\<Sum>j = 0..<l2. numbers2 ! j * \<omega> ^ (n div 2 ^ l * i * j) * \<omega> ^ (n div llen * i))"])
         subgoal 
           using fntt2_by_index[of i] that sum_in comm_semiring_1_class.semiring_normalization_rules(26)[of \<omega>]
           unfolding ntt_gen_def
           using sum_rules l2_def apply presburger
         done
         apply (rule sum_rules(2))
       subgoal for j
         using fntt2_by_index[of i] that sum_in comm_semiring_1_class.semiring_normalization_rules(26)[of \<omega>]
         unfolding ntt_gen_def
         apply auto
         done
       done
     have 009: "\<dots> = (\<Sum>j=0..<l2. (numbers ! (2*j+1) * \<omega>^((n div llen)*i*(2*j+1))))"
      apply (rule sum_rules(2))
       subgoal for j unfolding numbers2_def 
         apply(subst llen_def[symmetric])
           proof-
           assume ass: "j < l2 "
           hence "map ((!) numbers) (filter odd [0..<llen]) ! j = numbers ! (filter odd [0..<llen] ! j)"
             using  nth_map llen_def l2_def numbers2_def by (metis length_map)
           moreover have "filter odd [0..<llen] ! j = 2 * j +1" using
            filter_odd_nth Suc(2)  ass numbers2_def numbers2_even llen_def l2_def by fastforce
           moreover have "n div llen * (2 * j) = ((n div (2 ^ l))  * j)"
             using Suc(2) two_powrs_div[of l N] n_two_pot two_powr_div Suc(3) llen_def
             by (metis One_nat_def div_if mult.assoc nat_less_le not_less_eq numeral_2_eq_2 power_eq_0_iff power_inject_exp zero_neq_numeral)
           ultimately show 
             "map ((!) numbers) (filter odd [0..<llen]) ! j * \<omega> ^ (n div 2 ^ l * i * j + n div llen * i)
                 = numbers ! (2 * j + 1) * \<omega> ^ (n div llen * i * (2 * j + 1))" 
             by (smt (z3) Groups.mult_ac(2) distrib_left mult.right_neutral mult_2 mult_cancel_left)
         qed
         done
       have 010: " (fntt2!i) * (\<omega>^((n div llen) * i)) = (\<Sum>j=0..<l2. (numbers ! (2*j+1) * \<omega>^((n div llen)*i*(2*j+1)))) "
         using 008 009 by presburger
       have 011: " - (fntt2!i) * (\<omega>^((n div llen) * i)) =
                  (\<Sum>j=0..<l2. - (numbers ! (2*j+1) * \<omega>^((n div llen)*i*(2*j+1)))) "
         apply(rule neg_cong)
         apply(rule trans[of _ "fntt2 ! i * \<omega> ^ (n div llen * i)"])
         subgoal by simp
         apply(rule trans[where s="(\<Sum>j=0..<l2. (numbers ! (2*j+1) * \<omega>^((n div llen)*i*(2*j+1))))"])
          subgoal using 008 009 by simp 
         apply(rule sym)
         using sum_neg_in[of _ "l2"] 
         apply simp
         done
       have 012: "\<dots> = (\<Sum>j=0..<l2. (numbers ! (2*j+1) * \<omega>^((n div llen)*(2^l+i)*(2*j+1))))"
         apply(rule sum_rules(2))
         subgoal for j
           using Suc(2) Suc(3) omega_div_exp_min1[of l] llen_def l2_def
           apply (smt (z3) add.commute exp_rule mult.assoc mult_minus1_right plus_1_eq_Suc power_add power_minus1_odd power_mult)
           done
         done
       have 013:"fntt1 ! i = (\<Sum>j = 0..<2 ^ l. numbers!(2*j) * \<omega> ^ (n div llen * (2^l + i) * (2*j)))"
         using 005 006 007 numbers1_even llen_def  l1_def by auto
       have 014: "(\<Sum>j = 0..<2 ^ l. numbers ! (2*j + 1) * \<omega> ^ (n div llen* (2^l + i) * (2*j + 1))) =
                    - fntt2 ! i * \<omega> ^ (n div llen * i)"
      using  trans[OF l2_def numbers2_even]  sym[OF 012] sym[OF 011] by simp
      have "ntt_gen numbers llen (2 ^ l + i) = (fntt1!i) - (fntt2!i) * (\<omega>^((n div llen) * i))"
        unfolding ntt_gen_def apply(subst Suc(2))
        using  sum_splice[of "\<lambda> d.  numbers ! d  * \<omega> ^ (n div llen * (2^l+i) * d)" "2^l"] sym[OF 013]  014 Suc(2) by simp
       thus ?thesis using 000 sym[OF 001] "004" sum2_def by simp
     qed    
     then show ?thesis 
       by (metis "00" "01" list_eq_iff_nth_eq)
   qed
   obtain x y xs where xyxs: "numbers = x#y#xs" using Suc(2) 
     by (metis FNTT.cases add.left_neutral even_Suc even_add length_Cons list.size(3) mult_2 power_Suc power_eq_0_iff zero_neq_numeral)
   show ?case 
    apply(subst xyxs)
    apply(subst FNTT.simps(3))
    apply(subst xyxs[symmetric])+
     unfolding Let_def      
     using map_append[of "ntt_gen numbers llen" " [0..<llen div 2]" "[llen div 2..<llen]"] before_half after_half 
     unfolding llen_def sum1_def sum2_def fntt1_def fntt2_def NTT_gen_def
    apply (metis (no_types, lifting) Suc.prems(1) numbers1_def length_odd_filter mult_2 numbers2_def numbers2_even power_Suc upt_add_eq_append zero_le_numeral zero_le_power)
   done
qed

text \<open>\noindent \textbf{Major Correctness Theorem for Butterfly Algorithm}.\\
 
We have already shown:
\begin{itemize}
\item Generalized $NTT$ with degree annotation $2^N$ equals usual $NTT$.
\item Generalized $NTT$ tracks all levels of recursion in $FNTT$.
\end{itemize}
Thus, $FNTT$ equals $NTT$.
\<close>

theorem FNTT_correct:
  assumes "length numbers = n"
  shows "FNTT numbers = NTT numbers"
  using FNTT_NTT_gen_eq NTT_gen_NTT_full_length assms n_two_pot by force

subsection \<open>Inverse Transform in Butterfly Scheme\<close>

text \<open>We also formalized the inverse transform by using the butterfly scheme.
Proofs are obtained by adaption of arguments for $FNTT$.\<close>


lemmas [simp] = FNTT_termination_aux

fun IFNTT where
"IFNTT [] = []"|
"IFNTT [a] = [a]"|
"IFNTT nums = (let nn = length nums;
                  nums1 = [nums!i .  i <- (filter even [0..<nn])];
                  nums2 = [nums!i .  i <- (filter odd [0..<nn])];
                  ifntt1 = IFNTT nums1;
                  ifntt2 = IFNTT nums2;
                  sum1 = map2 (+) ifntt1 (map2 ( \<lambda> x k.  x*(\<mu>^( (n div nn) * k))) ifntt2 [0..<(nn div 2)]);
                  sum2 = map2 (-) ifntt1 (map2 ( \<lambda> x k.  x*(\<mu>^( (n div nn) * k))) ifntt2 [0..<(nn div 2)])
                   in sum1@sum2)"

lemmas [simp del] = FNTT_termination_aux


definition "intt_gen numbers degr i = (\<Sum>j=0..<(length numbers). (numbers ! j) * \<mu> ^((n div degr)*i*j)) "

definition "INTT_gen degr numbers = map (intt_gen numbers (degr)) [0..< length numbers]"

lemma INTT_gen_INTT_full_length: 
  assumes "length numbers =n"
  shows "INTT_gen n numbers = INTT numbers"
  unfolding INTT_gen_def intt_gen_def INTT_def intt_def 
  using assms by simp

lemma my_div_exp_min1:
  assumes "2^(Suc l) \<le> n"
  shows "(\<mu> ^(n div 2^(Suc l)))^(2^l) = -1" 
  by (metis assms divide_minus1 mult_zero_right mu_properties(1) nonzero_mult_div_cancel_right omega_div_exp_min1 power_one_over zero_neq_one)

lemma my_n_2_min1:  "\<mu>^(n div 2) = -1" 
  by (metis divide_minus1 mult_zero_right mu_properties(1) nonzero_mult_div_cancel_right omg_n_2_min1 power_one_over zero_neq_one)

text \<open>Correctness proof by common induction technique. Same strategies as for $FNTT$.\<close>

theorem IFNTT_INTT_gen_eq: 
 "length numbers = 2^l \<Longrightarrow> 2^l \<le> n \<Longrightarrow> IFNTT numbers = INTT_gen (length numbers) numbers"
proof(induction l arbitrary: numbers)
  case 0
  hence "local.IFNTT numbers = [numbers ! 0]" 
    by (metis IFNTT.simps(2) One_nat_def Suc_length_conv length_0_conv nth_Cons_0 power_0)
  then show ?case unfolding INTT_gen_def intt_gen_def 
    using 0 by simp
next
  case (Suc l)
  text \<open>We define some lists that are used during the recursive call.\<close>
  define numbers1 where "numbers1 = [numbers!i .  i <- (filter even [0..<length numbers])]" 
  define numbers2 where "numbers2 = [numbers!i .  i <- (filter odd [0..<length numbers])]" 
  define ifntt1 where "ifntt1 = IFNTT numbers1"
  define ifntt2 where "ifntt2 = IFNTT numbers2" 
  define sum1 where 
    "sum1 = map2 (+) ifntt1 (map2 ( \<lambda> x k.  x*(\<mu>^( (n div (length numbers)) * k))) 
                   ifntt2 [0..<((length numbers) div 2)])" 
  define sum2 where  
    "sum2 = map2 (-) ifntt1 (map2 ( \<lambda> x k.  x*(\<mu>^( (n div (length numbers)) * k))) 
                   ifntt2 [0..<((length numbers) div 2)])" 
  define l1 where "l1 = length numbers1"
  define l2 where "l2 = length numbers2"
  define llen where "llen = length numbers"

  text \<open>Properties of those lists\<close>
  have numbers1_even: "length numbers1 = 2^l" 
     using numbers1_def length_even_filter Suc by simp
   have numbers2_even: "length numbers2 = 2^l"
     using numbers2_def length_odd_filter Suc by simp
  have numbers1_ifntt: "ifntt1 = INTT_gen (2^l) numbers1" 
    using ifntt1_def Suc.IH[of numbers1] numbers1_even Suc(3) by simp
  hence ifntt1_by_index: "ifntt1 ! i = intt_gen numbers1 (2^l) i" if "i < 2^l" for i
    unfolding INTT_gen_def by (simp add: numbers1_even that)
  have numbers2_ifntt: "ifntt2 = INTT_gen (2^l) numbers2" 
    using ifntt2_def Suc.IH[of numbers2] numbers2_even Suc(3) by simp
  hence ifntt2_by_index: "ifntt2 ! i = intt_gen numbers2 (2^l) i" if "i < 2^l" for i
    unfolding INTT_gen_def by (simp add: numbers2_even that)
  have ifntt1_length: "length ifntt1 = 2^l" unfolding numbers1_ifntt INTT_gen_def numbers1_def
    using numbers1_def numbers1_even by force
   have ifntt2_length: "length ifntt2 = 2^l" unfolding numbers2_ifntt INTT_gen_def numbers2_def
     using numbers2_def numbers2_even by force

   text \<open>Same proof structure as for the  \textit{FNTT} proof.
         $\omega$s are just replaced by $\mu$s.\<close>
   have before_half: "map (intt_gen numbers llen) [0..<(llen div 2)] = sum1"
   proof-
 
     text \<open>Length is important, since we want to use list lemmas later on.\<close>
     have 00:"length (map (intt_gen numbers llen) [0..<(llen div 2)]) =  length sum1"
       unfolding sum1_def llen_def
       using Suc(2) map2_length[of _ ifntt2 "[0..<length numbers div 2]"]
       map2_length[of "(+)" ifntt1 "(map2 (\<lambda>x y. x * \<mu> ^ (n div length numbers * y)) ifntt2 [0..<length numbers div 2])"]
       ifntt1_length ifntt2_length by (simp add: mult_2)
     have 01:"length sum1 = 2^l" unfolding sum1_def 
       using "00" Suc.prems(1) sum1_def unfolding llen_def by auto

     text \<open>We show equality by extensionality on indices.\<close>
     have 02:"(map (intt_gen numbers llen) [0..<(llen div 2)]) ! i = sum1 ! i" 
       if "i < 2^l" for i
     proof-
       text \<open>First simplify this term.\<close>
       have 000:"(map (intt_gen numbers llen) [0..<(llen div 2)]) ! i =  intt_gen numbers llen i" 
         using "00" "01" that by auto

       text \<open>Expand the definition of $sum1$ and massage the result.\<close>
       moreover have 001:"sum1 ! i = (ifntt1!i) + (ifntt2!i) * (\<mu>^((n div llen) * i))"
         unfolding sum1_def using map2_index
         "00" "01" INTT_gen_def add.left_neutral diff_zero ifntt1_length length_map length_upt map2_map_map map_nth nth_upt numbers2_even numbers2_ifntt that llen_def by force
       moreover have 002:"(ifntt1!i) = (\<Sum>j=0..<l1. (numbers1 ! j) * \<mu>^((n div (2^l))*i*j))"
         unfolding l1_def
         using ifntt1_by_index[of i] that unfolding intt_gen_def by simp
       have 003:"... = (\<Sum>j=0..<l1. (numbers ! (2*j)) * \<mu>^((n div llen)*i*(2*j)))"
         apply (rule sum_rules(2))
         subgoal for j unfolding numbers1_def 
           apply(subst llen_def[symmetric])
         proof-
           assume ass: "j < l1 "
           hence "map ((!) numbers) (filter even [0..<length numbers]) ! j = numbers ! (filter even [0..<length numbers] ! j)"
             using  nth_map[of j "filter even [0..<length numbers]" "(!) numbers" ] 
             unfolding l1_def numbers1_def
             by (metis length_map)
           moreover have "filter even [0..<llen] ! j = 2 * j" using
            filter_even_nth[of j "llen" "2^l"] Suc(2)  ass numbers1_def numbers1_even 
             unfolding llen_def l1_def by fastforce
           moreover have "n div llen * (2 * j) = ((n div (2 ^ l))  * j)"
             using Suc(2) two_powrs_div[of l N] n_two_pot two_powr_div Suc(3) llen_def
             by (metis One_nat_def div_if mult.assoc nat_less_le not_less_eq numeral_2_eq_2 power_eq_0_iff power_inject_exp zero_neq_numeral)
           ultimately show "map ((!) numbers) (filter even [0..<llen]) ! j * \<mu> ^ (n div 2 ^ l * i * j) =
                   numbers ! (2 * j) * \<mu> ^ (n div llen * i * (2 * j))" 
             unfolding llen_def l1_def l2_def by (metis (mono_tags, lifting) mult.assoc mult.left_commute)
         qed
         done
       moreover have 004:
          "(ifntt2!i) * (\<mu>^((n div llen) * i)) = 
               (\<Sum>j=0..<l2.(numbers2 ! j) * \<mu>^((n div (2^l))*i*j+ (n div llen) * i))"
          apply(rule trans[where s = "(\<Sum>j = 0..<l2. numbers2 ! j * \<mu> ^ (n div 2 ^ l * i * j) * \<mu> ^ (n div llen * i))"])
         subgoal 
            unfolding l2_def llen_def
            using ifntt2_by_index[of i] that sum_in[of _ "(\<mu>^((n div llen) * i))" "l2"] comm_semiring_1_class.semiring_normalization_rules(26)[of \<mu>]
            unfolding intt_gen_def
            using sum_rules apply presburger
            done
          apply (rule sum_rules(2))
          subgoal for j
             using ifntt2_by_index[of i] that sum_in[of _ "(\<mu>^((n div llen) * i))" "l2"] comm_semiring_1_class.semiring_normalization_rules(26)[of \<mu>]
            unfolding intt_gen_def
            apply auto
            done
          done
     have 005: "\<dots> = (\<Sum>j=0..<l2. (numbers ! (2*j+1) * \<mu>^((n div llen)*i*(2*j+1))))"
      apply (rule sum_rules(2))
       subgoal for j unfolding numbers2_def 
         apply(subst llen_def[symmetric])
           proof-
           assume ass: "j < l2 "
           hence "map ((!) numbers) (filter odd [0..<llen]) ! j = numbers ! (filter odd [0..<llen] ! j)"
             using  nth_map unfolding l2_def numbers2_def llen_def by (metis length_map)
           moreover have "filter odd [0..<llen] ! j = 2 * j +1" using
            filter_odd_nth[of j "length numbers" "2^l"] Suc(2)  ass numbers2_def numbers2_even
             unfolding l2_def numbers2_def llen_def by fastforce
           moreover have "n div llen * (2 * j) = ((n div (2 ^ l))  * j)"
             using Suc(2) two_powrs_div[of l N] n_two_pot two_powr_div Suc(3) llen_def
             by (metis One_nat_def div_if mult.assoc nat_less_le not_less_eq numeral_2_eq_2 power_eq_0_iff power_inject_exp zero_neq_numeral)
           ultimately show 
            " map ((!) numbers) (filter odd [0..<llen]) ! j * \<mu> ^ (n div 2 ^ l * i * j + n div llen * i) 
                = numbers ! (2 * j + 1) * \<mu> ^ (n div llen * i * (2 * j + 1))" unfolding llen_def
             by (smt (z3) Groups.mult_ac(2) distrib_left mult.right_neutral mult_2 mult_cancel_left)
         qed
         done
       then show ?thesis 
         using 000 001 002 003 004 005 
         unfolding sum1_def llen_def l1_def l2_def
         using sum_splice_other_way_round[of "\<lambda> d.  numbers ! d  * \<mu> ^ (n div length numbers * i * d)" "2^l"] Suc(2)
         unfolding intt_gen_def 
         by (smt (z3) Groups.mult_ac(2) numbers1_even numbers2_even power_Suc2)
     qed
     then show ?thesis 
       by  (metis "00" "01" nth_equalityI)
   qed

   text \<open>We show index-wise equality for the second halves\<close>
   have after_half: "map (intt_gen numbers llen) [(llen div 2)..<llen] = sum2"
   proof-
     have 00:"length (map (intt_gen numbers llen) [(llen div 2)..<llen]) =  length sum2"
       unfolding sum2_def llen_def 
       using Suc(2) map2_length map2_length ifntt1_length ifntt2_length by (simp add: mult_2)
     have 01:"length sum2 = 2^l" unfolding sum1_def 
       using "00" Suc.prems(1) sum1_def llen_def  by auto

     text \<open>Equality for every index\<close>
     have 02:"(map (intt_gen numbers llen)  [(llen div 2)..<llen]) ! i = sum2 ! i" 
       if "i < 2^l" for i
     proof-
       have 000:"(map (intt_gen numbers llen)  [(llen div 2)..<llen]) ! i =  intt_gen numbers llen (2^l+i)"
         unfolding llen_def by (simp add: Suc.prems(1) that)
       have 001:" (map2 (\<lambda>x y. x * \<mu> ^ (n div llen * y)) ifntt2 [0..<llen div 2]) ! i =
                  ifntt2 ! i * \<mu> ^ (n div llen * i)"
         using  Suc(2) that by (simp add:  ifntt2_length  llen_def)
       have 003: "- ifntt2 ! i * \<mu> ^ (n div llen * i) = ifntt2 ! i * \<mu> ^ (n div llen * (i+ llen div 2))" 
         using Suc(2) my_div_exp_min1[of l] unfolding llen_def
         by (smt (z3) Suc.prems(2) mult.commute mult.left_commute mult_1s_ring_1(2) neq0_conv nonzero_mult_div_cancel_left numeral_One pos2 power_Suc power_add power_mult)
       hence 004:"sum2 ! i = (ifntt1!i) - (ifntt2!i) * (\<mu>^((n div llen) * i))"
         unfolding sum2_def llen_def 
         by (simp add: Suc.prems(1) ifntt1_length ifntt2_length that)
       have 005:"(ifntt1!i) = 
                     (\<Sum>j=0..<l1. (numbers1 ! j) * \<mu>^((n div (2^l))*i*j))"
        using ifntt1_by_index that unfolding intt_gen_def l1_def by simp
      have 006:"\<dots> =(\<Sum>j=0..<l1. (numbers ! (2*j)) * \<mu>^((n div llen)*i*(2*j)))"
         apply (rule sum_rules(2))
         subgoal for j unfolding numbers1_def 
          apply(subst llen_def[symmetric])
         proof-
           assume ass: "j < l1 "
           hence "map ((!) numbers) (filter even [0..<llen]) ! j = numbers ! (filter even [0..<llen] ! j)"
             using  nth_map unfolding llen_def l1_def numbers1_def by (metis length_map)
           moreover have "filter even [0..<llen] ! j = 2 * j" using
            filter_even_nth Suc(2)  ass numbers1_def numbers1_even llen_def l1_def by fastforce
           moreover have "n div llen * (2 * j) = ((n div (2 ^ l))  * j)"
             using Suc(2) two_powrs_div[of l N] n_two_pot two_powr_div Suc(3) llen_def
             by (metis One_nat_def div_if mult.assoc nat_less_le not_less_eq numeral_2_eq_2 power_eq_0_iff power_inject_exp zero_neq_numeral)
           ultimately show 
              "map ((!) numbers) (filter even [0..<llen]) ! j * \<mu> ^ (n div 2 ^ l * i * j) =
                        numbers ! (2 * j) * \<mu> ^ (n div llen * i * (2 * j))" 
             by (metis (mono_tags, lifting) mult.assoc mult.left_commute)
         qed
         done
        have 007:"\<dots> = (\<Sum>j=0..<l1. (numbers ! (2*j)) * \<mu> ^((n div llen)*(2^l + i)*(2*j))) "
         apply (rule sum_rules(2))
         subgoal for j 
           using Suc(2) Suc(3) my_div_exp_min1[of l] llen_def l1_def numbers1_def
           apply(smt (verit, del_insts) add.commute minus_power_mult_self mult_2 mult_minus1_right power_add power_mult)
           done
         done
       moreover have 008: "(ifntt2!i) * (\<mu>^((n div llen) * i)) =
                      (\<Sum>j=0..<l2. (numbers2 ! j) * \<mu>^((n div (2^l))*i*j+ (n div llen) * i))"
         apply(rule trans[where s = "(\<Sum>j = 0..<l2. numbers2 ! j * \<mu> ^ (n div 2 ^ l * i * j) * \<mu> ^ (n div llen * i))"])
         subgoal 
          using ifntt2_by_index[of i] that sum_in comm_semiring_1_class.semiring_normalization_rules(26)[of \<mu>]
          unfolding intt_gen_def
          using sum_rules l2_def apply presburger
         done
         apply (rule sum_rules(2))
       subgoal for j
         using ifntt2_by_index[of i] that sum_in comm_semiring_1_class.semiring_normalization_rules(26)[of \<mu>]
         unfolding intt_gen_def
         apply auto 
         done
       done
     have 009: "\<dots> = (\<Sum>j=0..<l2. (numbers ! (2*j+1) * \<mu>^((n div llen)*i*(2*j+1))))"
      apply (rule sum_rules(2))
       subgoal for j unfolding numbers2_def 
         apply(subst llen_def[symmetric])
           proof-
           assume ass: "j < l2 "
           hence "map ((!) numbers) (filter odd [0..<llen]) ! j = numbers ! (filter odd [0..<llen] ! j)"
             using  nth_map llen_def l2_def numbers2_def by (metis length_map)
           moreover have "filter odd [0..<llen] ! j = 2 * j +1" using
            filter_odd_nth Suc(2)  ass numbers2_def numbers2_even llen_def l2_def by fastforce
           moreover have "n div llen * (2 * j) = ((n div (2 ^ l))  * j)"
             using Suc(2) two_powrs_div[of l N] n_two_pot two_powr_div Suc(3) llen_def
             by (metis One_nat_def div_if mult.assoc nat_less_le not_less_eq numeral_2_eq_2 power_eq_0_iff power_inject_exp zero_neq_numeral)
           ultimately show 
             "map ((!) numbers) (filter odd [0..<llen]) ! j * \<mu> ^ (n div 2 ^ l * i * j + n div llen * i)
                 = numbers ! (2 * j + 1) * \<mu> ^ (n div llen * i * (2 * j + 1))" 
             by (smt (z3) Groups.mult_ac(2) distrib_left mult.right_neutral mult_2 mult_cancel_left)
         qed
         done
       have 010: " (ifntt2!i) * (\<mu>^((n div llen) * i)) = (\<Sum>j=0..<l2. (numbers ! (2*j+1) * \<mu>^((n div llen)*i*(2*j+1)))) "
         using 008 009 by presburger
       have 011: " - (ifntt2!i) * (\<mu>^((n div llen) * i)) =
                  (\<Sum>j=0..<l2. - (numbers ! (2*j+1) * \<mu>^((n div llen)*i*(2*j+1)))) "
         apply(rule neg_cong)
         apply(rule trans[where s="(\<Sum>j=0..<l2. (numbers ! (2*j+1) * \<mu>^((n div llen)*i*(2*j+1))))"])
         subgoal using 008 009 by simp
         apply(rule sym)
         using sum_neg_in[of _ "l2"] 
         apply simp
         done
       have 012: "\<dots> = (\<Sum>j=0..<l2. (numbers ! (2*j+1) * \<mu>^((n div llen)*(2^l+i)*(2*j+1))))"
         apply(rule sum_rules(2))
         subgoal for j
           using Suc(2) Suc(3) my_div_exp_min1[of l] llen_def l2_def
           apply (smt (z3) add.commute exp_rule mult.assoc mult_minus1_right plus_1_eq_Suc power_add power_minus1_odd power_mult)
           done
         done
       have 013:"ifntt1 ! i = (\<Sum>j = 0..<2 ^ l. numbers!(2*j) * \<mu> ^ (n div llen * (2^l + i) * (2*j)))"
         using 005 006 007 numbers1_even llen_def  l1_def by auto
       have 014: "(\<Sum>j = 0..<2 ^ l. numbers ! (2*j + 1) * \<mu> ^ (n div llen* (2^l + i) * (2*j + 1))) =
                    - ifntt2 ! i * \<mu> ^ (n div llen * i)"
      using  trans[OF l2_def numbers2_even]  sym[OF 012] sym[OF 011] by simp
      have "intt_gen numbers llen (2 ^ l + i) = (ifntt1!i) - (ifntt2!i) * (\<mu>^((n div llen) * i))"
        unfolding intt_gen_def 
        apply(subst Suc(2))
        using  sum_splice[of "\<lambda> d.  numbers ! d  * \<mu> ^ (n div llen * (2^l+i) * d)" "2^l"] sym[OF 013]  014 Suc(2) by simp
       thus ?thesis using 000 sym[OF 001] "004" sum2_def by simp
     qed    
     then show ?thesis 
       by (metis "00" "01" list_eq_iff_nth_eq)
   qed
   obtain x y xs where xyxs: "numbers = x#y#xs" using Suc(2) 
     by (metis FNTT.cases add.left_neutral even_Suc even_add length_Cons list.size(3) mult_2 power_Suc power_eq_0_iff zero_neq_numeral)
   show ?case 
    apply(subst xyxs)
    apply(subst IFNTT.simps(3))
    apply(subst xyxs[symmetric])+
     unfolding Let_def      
     using map_append[of "intt_gen numbers llen" " [0..<llen div 2]" "[llen div 2..<llen]"] before_half after_half 
     unfolding llen_def sum1_def sum2_def ifntt1_def ifntt2_def INTT_gen_def
    apply (metis (no_types, lifting) Suc.prems(1) numbers1_def length_odd_filter mult_2 numbers2_def numbers2_even power_Suc upt_add_eq_append zero_le_numeral zero_le_power)
   done
qed

text \<open>Correctness of the butterfly scheme for the inverse \textit{INTT}.\<close>

theorem IFNTT_correct:
  assumes "length numbers = n"
  shows "IFNTT numbers = INTT numbers"
  using IFNTT_INTT_gen_eq INTT_gen_INTT_full_length assms n_two_pot by force

text \<open>Also $FNTT$ and $IFNTT$ are mutually inverse\<close>

theorem IFNTT_inv_FNTT:  
  assumes "length numbers = n"
  shows "IFNTT (FNTT numbers) = map ((*) (of_int_mod_ring (int n))) numbers"
  by (simp add: FNTT_correct IFNTT_correct assms length_NTT ntt_correct)

text \<open>The other way round:\<close>

theorem FNTT_inv_IFNTT:  
  assumes "length numbers = n"
  shows "FNTT (IFNTT numbers) = map ((*) (of_int_mod_ring (int n))) numbers"
by (simp add: FNTT_correct IFNTT_correct assms inv_ntt_correct length_INTT)

subsection \<open>An Optimization\<close>
text \<open>Currently, we extract elements on even and odd positions respectively by a list comprehension 
     over even and odd indices. 
Due to the definition in Isabelle, an index access has linear time complexity. 
This results in quadratic running time complexity for every level
in the recursion tree of the \textit{FNTT}. 
In order to reach the $\mathcal{O}(n \log n)$ time bound, 
we have find a better way of splitting the elements at even or odd indices respectively.
\<close>

text \<open>A core of this optimization is the $evens\text{-}odds$ function,
 which splits the vectors in linear time.\<close>

fun evens_odds::"bool \<Rightarrow>'b list \<Rightarrow> 'b list" where
"evens_odds _ [] = []"|
"evens_odds True (x#xs)= (x# evens_odds False xs)"|
"evens_odds False (x#xs) = evens_odds True xs"

lemma map_filter_shift: " map f (filter even [0..<Suc g]) = 
        f 0 #  map (\<lambda> x. f (x+1)) (filter odd [0..<g])"
  by (induction g) auto

lemma map_filter_shift': " map f (filter odd [0..<Suc g]) = 
          map (\<lambda> x. f (x+1)) (filter even [0..<g])"
  by (induction g) auto

text \<open>A splitting by the $evens\text{-}odds$ function is 
equivalent to the more textbook-like list comprehension.\<close>

lemma filter_compehension_evens_odds:
      "[xs ! i. i <- filter even [0..<length xs]] = evens_odds True xs \<and>
       [xs ! i. i <- filter odd [0..<length xs]] = evens_odds False xs "
  apply(induction xs)
   apply simp
  subgoal for x xs
    apply rule
    subgoal 
      apply(subst evens_odds.simps)
      apply(rule trans[of _ "map ((!) (x # xs)) (filter even [0..<Suc (length xs)])"])
      subgoal by simp
      apply(rule trans[OF  map_filter_shift[of "(!) (x # xs)" "length xs"]])
      apply simp
      done

      apply(subst evens_odds.simps)
      apply(rule trans[of _ "map ((!) (x # xs)) (filter odd [0..<Suc (length xs)])"])
      subgoal by simp
      apply(rule trans[OF  map_filter_shift'[of "(!) (x # xs)" "length xs"]])
      apply simp
    done
  done

text \<open>For automated termination proof.\<close>

lemma [simp]: "length (evens_odds True vc) < Suc (length vc)" 
              "length (evens_odds False vc) < Suc (length vc)"
  by (metis filter_compehension_evens_odds le_imp_less_Suc length_filter_le length_map map_nth)+


text \<open>The $FNTT$ definition from above was suitable for matters of proof conduction.
   However, the naive decomposition into elements at odd and even indices induces a complexity of $n^2$ in every recursive step.
As mentioned, the $evens\text{-}odds$ function filters for elements on even or odd positions respectively.
The list has to be traversed only once which gives \textit{linear} complexity for every recursive step. \<close>

fun FNTT' where
"FNTT' [] = []"|
"FNTT' [a] = [a]"|
"FNTT' nums = (let nn = length nums;
                  nums1 = evens_odds  True nums;
                  nums2 = evens_odds False nums;
                  fntt1 = FNTT' nums1;
                  fntt2 = FNTT' nums2;
                  fntt2_omg =  (map2 ( \<lambda> x k.  x*(\<omega>^( (n div nn) * k))) fntt2 [0..<(nn div 2)]);
                  sum1 = map2 (+) fntt1 fntt2_omg;
                  sum2 = map2 (-) fntt1 fntt2_omg
                   in sum1@sum2)"

text \<open>The optimized \textit{FNTT} is equivalent to the naive \textit{NTT}.\<close>

lemma FNTT'_FNTT: "FNTT' xs = FNTT xs"
  apply(induction xs rule: FNTT'.induct)
  subgoal by simp
  subgoal by simp
  apply(subst FNTT'.simps(3))
  apply(subst FNTT.simps(3))
  subgoal for a b xs
    unfolding Let_def
    apply (metis filter_compehension_evens_odds)
    done
  done

text \<open>It is quite surprising that some inaccuracies in the interpretation of informal textbook definitions 
- even when just considering such a simple algorithm - can indeed affect time complexity.\<close>

subsection \<open>Arguments on Running Time\<close>

text \<open> $FFT$ is especially known for its $\mathcal{O}(n \log n)$ running time. 
Unfortunately, Isabelle does not provide a built-in time formalization. 
Nonetheless we can reason about running time after defining some "reasonable" consumption functions by hand.
Our approach loosely follows a general pattern by Nipkow et al.~\parencite{funalgs}.
First, we give running times and lemmas for the auxiliary functions used during FNTT.\\
General ideas behind the $\mathcal{O}(n \log n)$ are:
\begin{itemize}
\item By recursively halving the problem size, we obtain a tree of depth  $\mathcal{O}(\log n)$.
\item For every level of that tree, we have to process all elements which gives  $\mathcal{O}(n)$ time.
\end{itemize}

\<close>

text \<open>Time for splitting the list according to even and odd indices.\<close>

fun T_\<^sub>e\<^sub>o::"bool \<Rightarrow> 'c list \<Rightarrow> nat" where
" T_\<^sub>e\<^sub>o _ [] = 1"|
" T_\<^sub>e\<^sub>o True (x#xs)= (1+  T_\<^sub>e\<^sub>o False xs)"|
" T_\<^sub>e\<^sub>o  False (x#xs) = (1+  T_\<^sub>e\<^sub>o True xs)"

lemma T_eo_linear:  "T_\<^sub>e\<^sub>o b xs = length xs + 1"
  by (induction b xs rule: T_\<^sub>e\<^sub>o.induct) auto

text \<open>Time for length.\<close>

fun T\<^sub>l\<^sub>e\<^sub>n\<^sub>g\<^sub>t\<^sub>h where
"T\<^sub>l\<^sub>e\<^sub>n\<^sub>g\<^sub>t\<^sub>h [] = 1 "|
"T\<^sub>l\<^sub>e\<^sub>n\<^sub>g\<^sub>t\<^sub>h (x#xs) = 1+ T\<^sub>l\<^sub>e\<^sub>n\<^sub>g\<^sub>t\<^sub>h xs"

lemma T_length_linear: "T\<^sub>l\<^sub>e\<^sub>n\<^sub>g\<^sub>t\<^sub>h xs = length xs +1"
  by (induction xs) auto

text \<open>Time for index access.\<close>

fun T\<^sub>n\<^sub>t\<^sub>h where
"T\<^sub>n\<^sub>t\<^sub>h [] i = 1 "|
"T\<^sub>n\<^sub>t\<^sub>h (x#xs) 0 = 1"|
"T\<^sub>n\<^sub>t\<^sub>h (x#xs) (Suc i) = 1 + T\<^sub>n\<^sub>t\<^sub>h xs i"

lemma T_nth_linear: "T\<^sub>n\<^sub>t\<^sub>h xs i \<le> length xs +1"
  by (induction xs i rule: T\<^sub>n\<^sub>t\<^sub>h.induct) auto

text \<open>Time for mapping two lists into one result.\<close>

fun  T\<^sub>m\<^sub>a\<^sub>p\<^sub>2 where
 "T\<^sub>m\<^sub>a\<^sub>p\<^sub>2 t [] _ = 1"|
 "T\<^sub>m\<^sub>a\<^sub>p\<^sub>2 t  _ [] = 1"|
 "T\<^sub>m\<^sub>a\<^sub>p\<^sub>2 t (x#xs) (y#ys) = (t x y + 1 + T\<^sub>m\<^sub>a\<^sub>p\<^sub>2 t xs ys)"

lemma T_map_2_linear:
"c > 0 \<Longrightarrow>
       (\<And> x y. t x y \<le> c) \<Longrightarrow> T\<^sub>m\<^sub>a\<^sub>p\<^sub>2 t xs ys \<le> min (length xs) (length ys)  * (c+1) + 1"
  apply(induction t xs ys rule: T\<^sub>m\<^sub>a\<^sub>p\<^sub>2.induct)
  subgoal by simp
  subgoal by simp
  subgoal for t x xs y ys
    apply(subst  T\<^sub>m\<^sub>a\<^sub>p\<^sub>2.simps, subst length_Cons, subst length_Cons)
    using min_add_distrib_right[of 1]
    by (smt (z3) Suc_eq_plus1 add.assoc add.commute add_le_mono le_numeral_extra(4) min_def mult.commute mult_Suc_right)
  done

lemma T_map_2_linear':
"c > 0 \<Longrightarrow>
       (\<And> x y. t x y = c) \<Longrightarrow> T\<^sub>m\<^sub>a\<^sub>p\<^sub>2 t xs ys = min (length xs) (length ys)  * (c+1) + 1"
 by(induction t xs ys rule: T\<^sub>m\<^sub>a\<^sub>p\<^sub>2.induct) simp+
  

text \<open>Time for append.\<close>

fun T\<^sub>a\<^sub>p\<^sub>p where
 " T\<^sub>a\<^sub>p\<^sub>p  [] _ = 1"|
 " T\<^sub>a\<^sub>p\<^sub>p  (x#xs) ys = 1 +  T\<^sub>a\<^sub>p\<^sub>p  xs ys"

lemma T_app_linear: " T\<^sub>a\<^sub>p\<^sub>p xs ys = length xs +1"
  by(induction xs) auto


text \<open>Running Time of (optimized) $FNTT$.\<close>

fun T\<^sub>F\<^sub>N\<^sub>T\<^sub>T::"('a mod_ring) list \<Rightarrow> nat" where
"T\<^sub>F\<^sub>N\<^sub>T\<^sub>T [] = 1"|
"T\<^sub>F\<^sub>N\<^sub>T\<^sub>T [a] = 1"|
"T\<^sub>F\<^sub>N\<^sub>T\<^sub>T nums = (1 +T\<^sub>l\<^sub>e\<^sub>n\<^sub>g\<^sub>t\<^sub>h nums+ 3+
                 
                 (let nn = length nums;
                  nums1 = evens_odds True nums;
                  nums2 = evens_odds False nums
                  in 
                  T_\<^sub>e\<^sub>o True nums + T_\<^sub>e\<^sub>o False nums + 2 +
                 (let
                  fntt1 = FNTT nums1;
                  fntt2 = FNTT nums2
                  in 
                  (T\<^sub>F\<^sub>N\<^sub>T\<^sub>T nums1) + (T\<^sub>F\<^sub>N\<^sub>T\<^sub>T nums2) +
                 (let 
                  sum1 = map2 (+) fntt1 (map2 ( \<lambda> x k.  x*(\<omega>^( (n div nn) * k))) fntt2 [0..<(nn div 2)]);
                  sum2 = map2 (-) fntt1 (map2 ( \<lambda> x k.  x*(\<omega>^( (n div nn) * k))) fntt2 [0..<(nn div 2)])
                   in 
                    2* T\<^sub>m\<^sub>a\<^sub>p\<^sub>2 (\<lambda> x y. 1) fntt2 [0..<(nn div 2)] +
                      2* T\<^sub>m\<^sub>a\<^sub>p\<^sub>2 (\<lambda> x y. 1) fntt1 (map2 ( \<lambda> x k.  x*(\<omega>^( (n div nn) * k))) fntt2 [0..<(nn div 2)]) +
                    T\<^sub>a\<^sub>p\<^sub>p sum1 sum2))))"

lemma mono:  "((f x)::nat) \<le> f y \<Longrightarrow> f y \<le> fz \<Longrightarrow> f x \<le> fz" by simp

lemma evens_odds_length:
      "length (evens_odds True xs) = (length xs+1) div 2 \<and>
       length (evens_odds False xs) = (length xs) div 2"
 by(induction xs) simp+

text \<open>Length preservation during $FNTT$.\<close>

lemma FNTT_length: "length numbers = 2^l \<Longrightarrow> length (FNTT numbers) = length numbers" 
proof(induction l arbitrary: numbers)
  case (Suc l)
  define numbers1 where "numbers1 = [numbers!i .  i <- (filter even [0..<length numbers])]" 
  define numbers2 where "numbers2 = [numbers!i .  i <- (filter odd [0..<length numbers])]" 
  define fntt1 where "fntt1 = FNTT numbers1"
  define fntt2 where "fntt2 = FNTT numbers2" 
  define presum where 
    "presum = (map2 ( \<lambda> x k.  x*(\<omega>^( (n div (length numbers)) * k))) 
                   fntt2 [0..<((length numbers) div 2)])" 
  define sum1 where 
    "sum1 = map2 (+) fntt1 presum" 
   define sum2 where  
    "sum2 = map2 (-) fntt1 presum" 
  have "length numbers1  = 2^l" 
    by (metis Suc.prems numbers1_def diff_add_inverse2 length_even_filter mult_2 nonzero_mult_div_cancel_left power_Suc zero_neq_numeral)
  hence "length fntt1 = 2^l" 
    by (simp add: Suc.IH fntt1_def)
  hence "length presum = 2^l" unfolding presum_def 
    using map2_length Suc.IH Suc.prems fntt2_def length_odd_filter numbers2_def by force
   hence "length sum1 = 2^l" 
    by (simp add: \<open>length fntt1 = 2 ^ l\<close> sum1_def)
   have "length numbers2 = 2^l"
    by (metis Suc.prems numbers2_def length_odd_filter nonzero_mult_div_cancel_left power_Suc zero_neq_numeral)
  hence "length fntt2 = 2^l"
    by (simp add: Suc.IH fntt2_def)
  hence "length sum2 = 2^l" unfolding sum2_def  
    using \<open>length sum1 = 2 ^ l\<close> sum1_def by force
  hence final:"length (sum1@sum2) = 2^(Suc l)" 
    by (simp add: \<open>length sum1 = 2 ^ l\<close>)
  obtain x y xs where xyxs_Def: "numbers = x#y#xs"
    by (metis \<open>length numbers2 = 2 ^ l\<close> evens_odds.elims filter_compehension_evens_odds length_0_conv neq_Nil_conv numbers2_def power_eq_0_iff zero_neq_numeral)
  show ?case 
    apply(subst xyxs_Def, subst FNTT.simps(3), subst xyxs_Def[symmetric])
    unfolding Let_def
    using final 
    unfolding sum1_def sum2_def presum_def fntt1_def fntt2_def numbers1_def numbers2_def
    using Suc by (metis xyxs_Def)
qed (metis FNTT.simps(2) Suc_length_conv length_0_conv nat_power_eq_Suc_0_iff)
   
lemma add_cong: "(a1::nat) + a2+a3 +a4= b \<Longrightarrow> a1 +a2+ c + a3+a4= c +b"
  by simp

lemma add_mono:"a \<le> (b::nat) \<Longrightarrow> c \<le> d \<Longrightarrow> a + c \<le> b +d" by simp

lemma xyz: " Suc (Suc (length xs)) = 2 ^ l \<Longrightarrow> length (x # evens_odds True xs) = 2 ^ (l - 1)"
  by (metis (no_types, lifting) Nat.add_0_right Suc_eq_plus1 div2_Suc_Suc div_mult_self2 evens_odds_length length_Cons nat.distinct(1) numeral_2_eq_2 one_div_two_eq_zero plus_1_eq_Suc power_eq_if)

lemma zyx:" Suc (Suc (length xs)) = 2 ^ l  \<Longrightarrow> length (y # evens_odds False xs) = 2 ^ (l - 1)"
  by (smt (z3) One_nat_def Suc_pred diff_Suc_1 div2_Suc_Suc evens_odds_length le_numeral_extra(4) length_Cons nat_less_le neq0_conv power_0 power_diff power_one_right zero_less_diff zero_neq_numeral)

text \<open>When $length \; xs = 2^l$, then $length \; (evens\text{-}odds \; xs) = 2^{l-1}$.\<close>

lemma evens_odds_power_2:
  fixes x::'b and y::'b
  assumes "Suc (Suc (length (xs::'b list))) = 2 ^ l"
  shows " Suc(length (evens_odds b xs)) = 2 ^ (l-1)"
proof-
  have "Suc(length (evens_odds b xs)) = length (evens_odds b (x#y#xs))" 
    by (metis (full_types)  evens_odds.simps(2) evens_odds.simps(3) length_Cons)
  have "length (x#y#xs) = 2^l" using assms by simp
  have "length (evens_odds b (x#y#xs))  = 2^(l-1)" 
    apply (cases b)
    apply (smt (z3) Suc_eq_plus1 Suc_pred \<open>length (x # y # xs) = 2 ^ l\<close> add.commute add_diff_cancel_left' assms filter_compehension_evens_odds gr0I le_add1 le_imp_less_Suc length_even_filter mult_2 nat_less_le power_diff power_eq_if power_one_right zero_neq_numeral)
    by (smt (z3) One_nat_def Suc_inject \<open>length (x # y # xs) = 2 ^ l\<close> assms evens_odds_length le_zero_eq nat.distinct(1) neq0_conv not_less_eq_eq pos2 power_Suc0_right power_diff_power_eq power_eq_if)
   then show ?thesis 
    by (metis \<open>Suc (length (evens_odds b xs)) = length (evens_odds b (x # y # xs))\<close>)
qed

text \<open> \noindent \textbf{Major Lemma:} We rewrite the Running time of $FNTT$ in this proof and collect constraints for the time bound.
Using this, bounds are chosen in a way such that the induction goes through properly.
\paragraph \noindent We define:

\begin{equation*}
T(2^0) = 1
\end{equation*}

\begin{equation*}
T(2^l) = 
(2^l - 1)\cdot 14 apply+ 15 \cdot l \cdot 2^{l-1} + 2^l
\end{equation*}

\paragraph \noindent We want to show:

\begin{equation*}
T_{FNTT}(2^l) = T(2^l)
\end{equation*}

(Note that by abuse of types, the $2^l$ denotes a list of length $2^l$.)

\paragraph \noindent First, let's informally check that $T$ is indeed an accurate description of the running time:

\begin{align*}
T_{FNTT}(2^l) & \; =  14 + 15 \cdot  2 ^ {l-1} + 2 \cdot T_{FNTT}(2^{l-1}) \hspace{1cm} \text{by analyzing the running time function}\\
&\overset{I.H.}{=}  14 + 15 \cdot  2 ^ {l-1} + 2 \cdot  ((2^{l-1} - 1) \cdot 14 + (l - 1) \cdot 15 \cdot 2^{l-2} + 2^{l-1})\\
& \;= 14 \cdot 2^l - 14 + 15 \cdot  2 ^ {l-1} + 15\cdot l \cdot 2^{l-1} -  15 \cdot 2^{l-1} + 2^l\\
&\; = (2^l - 1)\cdot 14 + 15 \cdot l \cdot 2^{l-1} + 2^l\\
&\overset{def.}{=} T(2^l)
\end{align*}

The base case is trivially true.
\<close>

theorem tight_bound: 
  assumes T_def: "\<And> numbers l. length numbers = 2^l \<Longrightarrow> l > 0 \<Longrightarrow>
                               T numbers  = (2^l - 1) * 14 + l *15*2^(l-1) + 2^l"
                 "\<And> numbers l. l =0 \<Longrightarrow> length numbers = 2^l \<Longrightarrow> T numbers = 1"
  shows " length numbers = 2^l \<Longrightarrow> T\<^sub>F\<^sub>N\<^sub>T\<^sub>T numbers =  T numbers"
proof(induction numbers arbitrary: l rule: T\<^sub>F\<^sub>N\<^sub>T\<^sub>T.induct)
  case (3 x y numbers)

  text \<open>Some definitions for making term rewriting simpler.\<close>

  define  nn where "nn = length (x # y # numbers)" 
  define  nums1 where "nums1 = evens_odds True (x # y # numbers)" 
  define  nums2 where "nums2 = evens_odds False (x # y # numbers)"
  define fntt1  where "fntt1 = local.FNTT nums1"
  define fntt2 where "fntt2 = local.FNTT nums2"
  define sum1 where "sum1 = map2 (+) fntt1 (map2 (\<lambda>x y. x * \<omega> ^ (n div nn * y)) fntt2 [0..<nn div 2])"
  define sum2 where "sum2 = map2 (-) fntt1 (map2 (\<lambda>x y. x * \<omega> ^ (n div nn * y)) fntt2 [0..<nn div 2])"

  text \<open>Unfolding the running time function and combining it with the definitions above.\<close>

  have TFNNT_simp: " T\<^sub>F\<^sub>N\<^sub>T\<^sub>T (x # y # numbers) =
                    1 + T\<^sub>l\<^sub>e\<^sub>n\<^sub>g\<^sub>t\<^sub>h (x # y # numbers) + 3 +  
                    T_\<^sub>e\<^sub>o True (x # y # numbers) + T_\<^sub>e\<^sub>o False (x # y # numbers) + 2 +
                    local.T\<^sub>F\<^sub>N\<^sub>T\<^sub>T nums1 + local.T\<^sub>F\<^sub>N\<^sub>T\<^sub>T nums2 +
                    2 * T\<^sub>m\<^sub>a\<^sub>p\<^sub>2 (\<lambda>x y. 1) fntt2 [0..<nn div 2] +
                    2 *
                    T\<^sub>m\<^sub>a\<^sub>p\<^sub>2 (\<lambda>x y. 1) fntt1 (map2 (\<lambda>x y. x * \<omega> ^ (n div nn * y)) fntt2 [0..<nn div 2]) +
                    T\<^sub>a\<^sub>p\<^sub>p sum1 sum2" 
    apply(subst  T\<^sub>F\<^sub>N\<^sub>T\<^sub>T.simps(3))
    unfolding Let_def unfolding sum2_def sum1_def fntt1_def fntt2_def nums1_def nums2_def nn_def
    apply simp
    done

  text \<open>Application of lemmas related to running times of auxiliary functions.\<close>

  have length_nums1: "length nums1 = (2::nat)^(l-1)"
    unfolding nums1_def
    using evens_odds_length[of "x # y # numbers"] 3(3) xyz by fastforce
 have length_nums2: "length nums2 = (2::nat)^(l-1)"
    unfolding nums2_def
    using evens_odds_length[of "x # y # numbers"] 3(3) 
    by (metis One_nat_def le_0_eq length_Cons lessI list.size(4) neq0_conv not_add_less2 not_less_eq_eq pos2 power_Suc0_right power_diff_power_eq power_eq_if)
  have length_simp: "T\<^sub>l\<^sub>e\<^sub>n\<^sub>g\<^sub>t\<^sub>h (x # y # numbers) = (2::nat) ^l +1"
    using T_length_linear[of "x#y#numbers"]  3(3)  by simp
  have even_odd_simp: " T_\<^sub>e\<^sub>o b (x # y # numbers) = (2::nat)^l + 1" for b
    by (metis "3.prems" T_eo_linear)+
  have 02: "(length fntt2) =  (length [0..<nn div 2])" unfolding fntt2_def 
    apply(subst FNTT_length[of _ "l-1"])
    unfolding nums2_def
    using length_nums2 nums2_def apply fastforce 
    by (simp add: evens_odds_length nn_def)
  have 03: "(length fntt1) =  (length [0..<nn div 2])" unfolding fntt1_def 
    apply(subst FNTT_length[of _ "l-1"])
    unfolding nums1_def
    using length_nums1 nums1_def apply fastforce
    by (metis "02" FNTT_length fntt2_def length_nums1 length_nums2 nums1_def)
  have map21_simp: "T\<^sub>m\<^sub>a\<^sub>p\<^sub>2 (\<lambda>x y. 1) fntt2 [0..<nn div 2] = (2::nat)^l + 1"
    apply(subst T_map_2_linear'[of 1])
    subgoal by simp subgoal by simp 
    by (smt (z3) "02" "3"(3) FNTT_length div_less evens_odds_length fntt2_def length_nums2 lessI less_numeral_extra(3) min.idem mult.commute nat_1_add_1 nums2_def plus_1_eq_Suc power_eq_if power_not_zero zero_power2)
  have map22_simp: "T\<^sub>m\<^sub>a\<^sub>p\<^sub>2 (\<lambda>x y. 1) fntt1 (map2 (\<lambda>x y. x * \<omega> ^ (n div nn * y)) fntt2 [0..<nn div 2]) =
        (2::nat)^l + 1"
    apply(subst T_map_2_linear'[of 1])
    subgoal by simp subgoal by simp apply simp
    unfolding fntt1_def fntt2_def unfolding nn_def
    apply(subst FNTT_length[of _ "l-1"], (rule length_nums1)?, (rule length_nums2)?,
                 (subst length_nums1)?,  (subst length_nums2)?,  (subst 3(3))?)+
    apply (metis (no_types, lifting) "3"(3) div_less evens_odds_length length_nums2 lessI min_def mult_2 nat_1_add_1 nums2_def plus_1_eq_Suc power_eq_if power_not_zero zero_neq_numeral)
    done
  have sum1_simp: "length sum1 = 2^(l-1)"
    unfolding sum1_def
    apply(subst map2_length)+
    apply(subst 02, subst 03) 
    unfolding nn_def using 3(3)
    by (metis "02" FNTT_length fntt2_def length_nums2 min.idem nn_def)
  have app_simp: "T\<^sub>a\<^sub>p\<^sub>p sum1 sum2 = (2::nat)^(l-1) + 1"
    by(subst T_app_linear, subst sum1_simp, simp)
  let ?T1 = "(2^(l-1) - 1) * 14 + (l-1) *15*2^(l-1 -1) + 2^(l-1)"

  text \<open>Induction hypotheses\<close>

  have IH_pluged1: "local.T\<^sub>F\<^sub>N\<^sub>T\<^sub>T nums1 = ?T1"
     apply(subst "3.IH"(1)[of nn nums1 nums2 fntt1 fntt2 "l-1", 
                            OF nn_def nums1_def nums2_def fntt1_def fntt2_def length_nums1])
     apply(cases "l \<le> 1")
    subgoal
      apply(subst T_def(2)[of "l-1"])
      subgoal by simp
       apply(rule length_nums1)
      apply simp
      done      
     apply(subst T_def(1)[OF length_nums1])
    subgoal by simp
    subgoal by simp
    done

    have IH_pluged2: "local.T\<^sub>F\<^sub>N\<^sub>T\<^sub>T nums2 = ?T1"
     apply(subst "3.IH"(2)[of nn nums1 _ fntt1 fntt2 "l-1", OF nn_def nums1_def nums2_def fntt1_def
                           fntt2_def length_nums2 ])
     apply(cases "l \<le> 1")
    subgoal
      apply(subst T_def(2)[of "l-1"])
      subgoal by simp
       apply(rule length_nums2)
      apply simp
      done      
     apply(subst T_def(1)[OF length_nums2])
    subgoal by simp
    subgoal by simp
    done
    
  have " T\<^sub>F\<^sub>N\<^sub>T\<^sub>T (x # y # numbers) =    
        14 + (3 * 2 ^ l + (local.T\<^sub>F\<^sub>N\<^sub>T\<^sub>T nums1 +
        (local.T\<^sub>F\<^sub>N\<^sub>T\<^sub>T nums2 + (5 * 2^(l-1) + 4 * (2 ^ l div 2)))))"
    apply(subst TFNNT_simp, subst map21_simp, subst map22_simp, subst  length_simp,
          subst app_simp, subst even_odd_simp, subst even_odd_simp)
    apply(auto simp add: algebra_simps power_eq_if[of 2 l])
    done

  text \<open>Proof that the term $T\text{-}def$ indeed fulfills the recursive properties, i.e.
          $t(2^l) = 2 \cdot t(2^{l-1}) + s$\<close>

  also have "\<dots> = 14 + (3 * 2 ^ l + (?T1 + (?T1 + (5 * 2^(l-1) + 4 * (2 ^ l div 2)))))" 
    apply(subst IH_pluged1, subst IH_pluged2) 
    by simp
  also have "\<dots> =  14 + (6 * 2 ^ (l-1) +
          2*((2 ^ (l - 1) - 1) * 14 + (l - 1) * 15 * 2 ^ (l - 1 - 1) + 2 ^ (l - 1)) +
       (5 * 2 ^ (l - 1) + 4 * (2 ^ l div 2)))"
    by (smt (verit) "3"(3) add.assoc div_less evens_odds_length left_add_twice length_nums2 lessI mult.assoc mult_2_right nat_1_add_1 numeral_Bit0 nums2_def plus_1_eq_Suc power_eq_if power_not_zero zero_neq_numeral)
  also have "\<dots> =  14 +  15 * 2 ^ (l-1) +
     2*((2 ^ (l - 1) - 1) * 14 + (l - 1) * 15 * 2 ^ (l - 1 - 1) + 2 ^ (l - 1))" 
    by (smt (z3) "3"(3) add.assoc add.commute calculation diff_diff_left distrib_left div2_Suc_Suc evens_odds_length left_add_twice length_Cons length_nums2 mult.assoc mult.commute mult_2 mult_2_right numeral_Bit0 numeral_Bit1 numeral_plus_numeral nums2_def one_add_one)
  also have "... = 14 + 15 * 2 ^ (l-1) +
                    (2 ^ l - 2) * 14 + (l - 1) * 15 * 2 ^ (l - 1) + 2 ^ l"
    apply(cases "l > 1")
    apply (smt (verit, del_insts) add.assoc diff_is_0_eq distrib_left_numeral left_diff_distrib' less_imp_le_nat mult.assoc mult_2 mult_2_right nat_1_add_1 not_le not_one_le_zero power_eq_if)
    by (smt (z3) "3"(3) add.commute add.right_neutral cancel_comm_monoid_add_class.diff_cancel diff_add_inverse2 diff_is_0_eq div_less_dividend evens_odds_length length_nums2 mult_2 mult_eq_0_iff nat_1_add_1 not_le nums2_def power_eq_if)
  also have "\<dots> =  15 * 2 ^ (l - 1) + (2 ^ l - 1) * 14 + (l - 1) * 15 * 2 ^ (l - 1) + 2 ^ l"
    by (smt (z3) "3"(3) One_nat_def add.commute combine_common_factor diff_add_inverse2 diff_diff_left list.size(4) nat_1_add_1 nat_mult_1)
  also have "\<dots> = (2^l - 1) * 14 + l *15*2^(l-1) + 2^l" 
    apply(cases "l > 0")
    subgoal using group_cancel.add1 group_cancel.add2 less_numeral_extra(3) mult.assoc mult_eq_if by auto[1]
    using "3"(3) by fastforce

  text \<open>By the previous proposition, we can conclude that $T$ is indeed a suitable term for describing the running time\<close>

  finally have "T\<^sub>F\<^sub>N\<^sub>T\<^sub>T (x # y # numbers) = T (x # y # numbers)"
    using T_def(1)[of "x#y#numbers" l] 
    by (metis "3.prems" bits_1_div_2 diff_is_0_eq' evens_odds_length length_nums2 neq0_conv nums2_def power_0 zero_le_one zero_neq_one)
  thus ?case by simp
qed (auto simp add: assms)

text \<open>We can finally state that $FNTT$ has $\mathcal{O}(n \log n)$ time complexity.\<close>

theorem log_lin_time:
  assumes "length numbers = 2^l"
  shows "T\<^sub>F\<^sub>N\<^sub>T\<^sub>T  numbers \<le> 30 * l * length numbers + 1"
proof-
  have 00: "T\<^sub>F\<^sub>N\<^sub>T\<^sub>T  numbers  = (2 ^ l - 1) * 14 + l * 15 * 2 ^ (l - 1) + 2 ^ l"
    using tight_bound[of "\<lambda> xs. (length xs - 1) * 14 + (Discrete.log (length xs)) * 15 * 
                            2 ^ ( (Discrete.log (length xs)) - 1) + length xs" numbers l] 
          assms by simp
  have " l * 15 * 2 ^ (l - 1) \<le> 15 * l * length numbers" using assms by simp
  moreover have "(2 ^ l - 1) * 14  + 2^l\<le> 15 * length numbers " 
    using assms by linarith
  moreover hence "(2 ^ l - 1) * 14 + 2^l \<le> 15 * l * length numbers +1"  using assms 
    apply(cases l)
    subgoal by simp 
    by (metis (no_types) add.commute le_add1 mult.assoc mult.commute
          mult_le_mono nat_mult_1 plus_1_eq_Suc trans_le_add2)
  ultimately have " (2 ^ l - 1) * 14 + l * 15 * 2 ^ (l - 1) + 2 ^ l \<le>  30 * l * length numbers +1"
    by linarith
  then show  ?thesis using 00 by simp
qed

theorem log_lin_time_explicitly:
  assumes "length numbers = 2^l"
  shows "T\<^sub>F\<^sub>N\<^sub>T\<^sub>T  numbers \<le> 30 * Discrete.log (length numbers) * length numbers + 1"
  using log_lin_time[of numbers l] assms by simp

end
end
