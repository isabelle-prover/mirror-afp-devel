(*
Title: Number Theoretic Transform
Author: Thomas Ammer
*)

theory NTT
  imports Preliminary_Lemmas
begin

section \<open>Number Theoretic Transform and Inverse Transform\<close>
text \<open>\label{NTT}\<close>

locale ntt = preliminary "TYPE ('a ::prime_card)" +
fixes \<omega> :: "('a::prime_card mod_ring)"
fixes \<mu> :: "('a mod_ring)"
assumes omega_properties: "\<omega>^n = 1" "\<omega> \<noteq> 1" "(\<forall> m. \<omega>^m = 1 \<and> m\<noteq>0 \<longrightarrow> m \<ge> n)"
assumes mu_properties: "\<mu> * \<omega> = 1"
begin

lemma mu_properties': "\<mu> \<noteq> 1"
  using omega_properties mu_properties by auto

subsection \<open>Definition of $NTT$ and $INTT$\<close>
text \<open>\label{NTTdef}\<close>

text \<open>
Now we can state an analogue to the $DFT$ on finite fields, 
namely the \textit{Number Theoretic Transform}.
First, let us look at an informal definition of $\mathsf{NTT}$~\parencite{ntt_intro}:
\begin{equation*}
\mathsf{NTT}(\vec{x}) = 
\begin{pmatrix}
 1 &     1  &        1 &     1    &  \cdots&           1 \\
 1 & \omega   & \omega^2 & \omega^3 & \cdots & \omega^{n-1} \\
 1 & \omega^2 & \omega^4 & \omega^6 & \cdots & \omega^{2\cdot(n-1)} \\
 1 & \omega^3 & \omega^6 & \omega^9 & \cdots & \omega^{3\cdot(n-1)} \\
\vdots &  \vdots &  \vdots &  \vdots  &        &      \vdots          \\
 1 & \omega^{n-1} & \omega^{2\cdot(n-1)} & \omega^{3\cdot(n-1)} & \cdots & \omega^{(n-1)\cdot(n-1)} 
\end{pmatrix} \cdot \vec{x}
\end{equation*}

Or for single vector entries:
\begin{equation*}
\mathsf{NTT}(\vec{x})_i = \sum _{j = 0} ^{n-1} x_j \cdot \omega ^{i\cdot j} 
\end{equation*}

\<close>

text \<open>Formally:\<close>

definition ntt::"(('a ::prime_card) mod_ring) list \<Rightarrow> nat \<Rightarrow> 'a mod_ring" where
"ntt numbers i = (\<Sum>j=0..<n. (numbers ! j) * \<omega>^(i*j)) "

definition "NTT numbers = map (ntt numbers) [0..<n]"


text \<open>\label{INTTdef}
We define the inverse transform $\mathsf{INTT}$ by matrices:
\begin{equation*}
 \mathsf{INTT}(\vec{y}) = 
\begin{pmatrix}
 1 &     1  &        1 &     1    &  \cdots&           1 \\
 1 & \mu   & \mu^2 & \mu^3 & \cdots & \mu^{n-1} \\
 1 & \mu^2 & \mu^4 & \mu^6 & \cdots & \mu^{2\cdot(n-1)} \\
 1 & \mu^3 & \mu^6 & \mu^9 & \cdots & \mu^{3\cdot(n-1)} \\
\vdots &  \vdots &  \vdots &  \vdots  &        &      \vdots          \\
 1 & \mu^{n-1} & \mu^{2\cdot(n-1)} & \mu^{3\cdot(n-1)} & \cdots & \mu^{(n-1)\cdot(n-1)} 
\end{pmatrix} \cdot \vec{y}
\end{equation*}
Per component: 
\begin{equation*}
%
\mathsf{INTT}(\vec{y})_i = \sum _{j = 0} ^{n-1} y_j \cdot \mu ^{i\cdot j} 
%
\end{equation*}

\<close>

definition "intt xs i = (\<Sum>j=0..<n. (xs ! j) * \<mu>^(i*j)) "

definition "INTT xs = map (intt xs) [0..<n]"

text \<open>Vector length is preserved.\<close>

lemma length_NTT:
  assumes n_def: "length numbers = n"
  shows "length (NTT numbers) = n"
  unfolding NTT_def ntt_def using n_def length_map[of _ "[0..<n]"]
  by simp

lemma length_INTT:
  assumes n_def: "length numbers = n"
  shows "length (INTT numbers) = n"
  unfolding INTT_def intt_def using n_def length_map[of _ "[0..<n]"]
  by simp

subsection \<open>Correctness Proof of $NTT$ and $INTT$\<close>
text \<open>\label{NTTcorr}\<close>
text \<open>
We prove $\mathsf{NTT}$ and $\mathsf{INTT}$ correct:
By taking $\mathsf{INTT}(\mathsf{NTT} (x))$ we obtain $x$ scaled by $n$.
Analogue to $DFT$, one can get rid of the factor $n$ by a simple rescaling.
First, consider an informal proof sketch using the matrix form:
\begin{equation*}
\begin{split}
\mathsf{INTT}(\mathsf{NTT}(\vec{x})) = \hspace{11cm}\\
%
\begin{pmatrix}
 1 &     1  &            1    &  \cdots&           1 \\
 1 & \mu   & \mu^2 &  \cdots & \mu^{n-1} \\
 1 & \mu^2 & \mu^4 &  \cdots & \mu^{2\cdot(n-1)} \\
\vdots &  \vdots &    \vdots  &        &      \vdots          \\
 1 & \mu^{n-1} & \mu^{2\cdot(n-1)}& \cdots & \mu^{(n-1)\cdot(n-1)} 
\end{pmatrix}
%
\cdot
%
\begin{pmatrix}
 1 &     1  &        1 &  \cdots&           1 \\
 1 & \omega   & \omega^2 & \cdots & \omega^{n-1} \\
 1 & \omega^2 & \omega^4  & \cdots & \omega^{2\cdot(n-1)} \\
\vdots &  \vdots &  \vdots  &        &      \vdots          \\
 1 & \omega^{n-1} & \omega^{2\cdot(n-1)} & \cdots & \omega^{(n-1)\cdot(n-1)} 
\end{pmatrix} 
\cdot
%
\vec{x}
%
\end{split}
\end{equation*}

A resulting entry is of the following form:

\begin{equation*}
%
\mathsf{INTT}(\mathsf{NTT}(x))_i = \sum _ {j = 0} ^{n-1} (\sum _{k = 0} ^{n-1} \mu^{i\cdot k} \cdot \omega^{j\cdot k}) \cdot x_j
%
\end{equation*}

Now, we analyze the interior sum by cases on $i = j$.

\paragraph \noindent Case $i = j$.
\begin{align*}
\sum _{k = 0} ^{n-1} \mu^{i\cdot k} \cdot \omega^{j\cdot k}
&= \sum _{k = 0} ^{n-1} (\mu \cdot \omega)^{i \cdot k} \\
&= n \cdot (\mu \cdot \omega)^{i \cdot k} \\
&=  n \cdot 1 ^{i \cdot k} \\ &= n
\end{align*}
Note that $\omega$ and $\mu$ are mutually inverse.
\paragraph \noindent Case $i \neq j$. Wlog assume $i > j$, otherwise replace $\omega$ by $\mu$ and $i -j$ by $j - i$ respectively.
\begin{align*}
\sum _{k = 0} ^{n-1} \mu^{i\cdot k} \cdot \omega^{j\cdot k}
&= \sum _{k = 0} ^{n-1} (\mu \cdot \omega)^{j \cdot k} \cdot \omega^{(i-j) \cdot k} \\
&= \sum _{k = 0} ^{n-1} \omega^{(i-j) \cdot k} \\
&=  (1 - \omega ^{(i-j)\cdot n}) \cdot (1 - \omega^{i-j})^{-1} && \text{by lemma on geometric sum}\\
&=  (1 - 1^n) \cdot (1 - \omega^{i-j})^{-1} \\
&= 0
\end{align*}

We conclude that $\sum \limits _ {j = 0} ^{n-1} (\sum \limits _{k = 0} ^{n-1} \mu^{i\cdot k} \cdot \omega^{j\cdot k}) \cdot x_j = n \cdot x_i$.

\<close>

theorem ntt_correct: 
  assumes n_def: "length numbers = n"
  shows "INTT (NTT numbers) = map (\<lambda> x. (of_int_mod_ring n) * x ) numbers"
proof-
  have 0:"\<And> i. i < n \<Longrightarrow> (INTT (NTT numbers)) ! i = intt (NTT numbers) i " using n_def length_NTT
    unfolding INTT_def NTT_def intt_def by simp

  text \<open>Major sublemma.\<close>

  have 1:"\<And> i. i < n \<Longrightarrow>intt (NTT numbers) i = (of_int_mod_ring n)*numbers ! i"
  proof-
    fix i
    assume i_assms:"i < n"

    text \<open>First, simplify by some chains of equations.\<close>

    hence 1:"intt (NTT numbers) i  =
            (\<Sum>l = 0..<n. 
              (\<Sum>j = 0..<n. numbers ! j * \<omega> ^ (l * j)) * \<mu> ^ (i * l))" 
      unfolding NTT_def intt_def ntt_def using n_def length_map nth_map by simp
    also have 2:"\<dots> =
            (\<Sum>l = 0..<n. 
              (\<Sum>j = 0..<n. (numbers ! j * \<omega> ^ (l * j)) * \<mu> ^ (i * l)))"
      using sum_in by (simp add: sum_distrib_right) 
    also have 3:"\<dots> =
            (\<Sum>j = 0..<n. 
              (\<Sum>l = 0..<n. (numbers ! j * \<omega> ^ (l * j) * \<mu> ^ (i * l))))" using sum_swap by fast

    text \<open>As in the informal proof, we consider three cases. First $j = i$.\<close>

    have iisj:"\<And> j. j = i \<Longrightarrow> (\<Sum>l = 0..<n. (numbers ! j * \<omega> ^ (l * j) * \<mu> ^ (i * l))) = (numbers ! j)* (of_int_mod_ring n)"
    proof-
      fix j
      assume "j=i"
      hence "\<And> l. l < n \<Longrightarrow> (numbers ! j * \<omega> ^ (l * j) * \<mu> ^ (i * l))= (numbers ! j)"
        by (simp add: left_right_inverse_power mult.commute mu_properties(1))
      moreover have "\<And> l. l < n  \<Longrightarrow> numbers ! j *  \<omega> ^ (l * j) * \<mu> ^ (i * l) = numbers ! j" 
        using calculation by blast

      text \<open>$\omega^{il}\cdot \omega^{jl} = 1$. Thus, we sum over $1$ $n$ times, which gives the goal.\<close>

      ultimately show "(\<Sum>l = 0..<n. (numbers ! j * \<omega> ^ (l * j) * \<mu> ^ (i * l))) = 
        (numbers ! j)* (of_int_mod_ring n)" 
        using n_def sum_const[of "numbers ! j" n] exp_rule[of \<omega> \<mu>] mu_properties(1) 
        by (metis (no_types, lifting) atLeastLessThan_iff mult.commute sum.cong) 

    qed

    text \<open>Case $j < i$.\<close>

    have jlsi:"\<And> j. j < i \<Longrightarrow> (\<Sum>l = 0..<n. (numbers ! j * \<omega> ^ (l * j) * \<mu> ^ (i * l))) = 0"
    proof-
      fix j
      assume j_assms:"j < i"
      hence 00:"\<And>  (c::('a::prime_card) mod_ring) a b. c * a^j*b^i  = (a*b)^j*(c * b^(i-j))" 
         using  algebra_simps 
         by (smt (z3) le_less ordered_cancel_comm_monoid_diff_class.add_diff_inverse power_add)

       text \<open>A geometric sum over $\mu^l$ remains.\<close>

      have 01:" (\<Sum>l = 0..<n. (numbers ! j * \<omega> ^ (l * j) * \<mu> ^ (i * l))) = 
                (\<Sum>l = 0..<n. (numbers ! j *  (\<mu>^l)^(i-j)))" 
           apply(rule sum_eq)
           using mu_properties(1) 00 algebra_simps(23)
           by (smt (z3) mult.commute mult.left_neutral power_mult power_one)
      have 02:"\<dots> = numbers ! j *(\<Sum>l = 0..<n. ((\<mu>^l)^(i-j))) " 
           using sum_in[of "\<lambda> l. numbers ! j * (\<mu> ^ l) ^ (i - j)" " numbers ! j" n] 
           by (simp add: mult_hom.hom_sum)
      moreover have 03:"(\<Sum>l = 0..<n. ((\<mu>^l)^(i-j))) = 
                     (\<Sum>l = 0..<n. ((\<mu>^(i-j))^l)) "
        by(rule sum_eq) (metis mult.commute power_mult)
      have "\<mu>^(i-j) \<noteq> 1" 
      proof
        assume "\<mu> ^ (i - j) = 1"
        hence "ord p (to_int_mod_ring \<mu>) \<le> i-j" 
          by (simp add: j_assms not_le ord_max)
        moreover hence "ord p (to_int_mod_ring \<omega>) \<le> i-j" 
          by (metis \<open>\<mu> ^ (i - j) = 1\<close> diff_is_0_eq exp_rule j_assms leD mult.comm_neutral mult.commute mu_properties(1) ord_max)
        moreover hence "i-j < n" 
          using j_assms i_assms p_fact k_bound n_lst2 by linarith
        moreover have "ord p (to_int_mod_ring \<omega>) = n" using omega_properties n_lst2 unfolding ord_def          
          by (metis (no_types) \<open>\<mu> ^ (i - j) = 1\<close> calculation(3) diff_is_0_eq j_assms leD left_right_inverse_power mult.comm_neutral mult_cancel_left mu_properties(1) omega_properties(3) zero_neq_one)
        ultimately show False by simp
      qed

      text \<open>Application of the lemma for geometric sums.\<close>

      ultimately have "(1-\<mu>^(i-j))*(\<Sum>l = 0..<n. ((\<mu>^(i-j))^l)) = (1-(\<mu>^(i-j))^n)" 
        using geo_sum[of "\<mu> ^ (i - j)" n] by simp
      moreover have "(\<mu>^(i-j))^n = 1"
        by (metis (no_types) left_right_inverse_power mult.commute mult.right_neutral mu_properties(1) omega_properties(1) power_mult power_one)

      text \<open>The sum for the current index is 0.\<close>
      
      ultimately have "(\<Sum>l = 0..<n. ((\<mu>^(i-j))^l)) = 0"
        by (metis \<open>\<mu> ^ (i - j) \<noteq> 1\<close> divisors_zero eq_iff_diff_eq_0)
      thus "(\<Sum>l = 0..<n. numbers ! j * \<omega> ^ (l * j) * \<mu> ^ (i * l)) = 0" using  01 02 03 by simp
    qed

    text \<open>Case $i < j$. 
       We also rewrite the whole summation until the lemma for geometric sums is applicable.
       From this, we conclude that the term is 0.\<close>

    have ilsj:"\<And> j. i < j \<and> j < n \<Longrightarrow> (\<Sum>l = 0..<n. (numbers ! j * \<omega> ^ (l * j) * \<mu> ^ (i * l))) = 0"
    proof-
      fix j
      assume ij_Assm: "i < j \<and> j < n"
      hence 00:"\<And>  (c::('a::prime_card) mod_ring) a b. (a*b)^i*(c * b^(j-i)) = c * a^i*b^j  " 
        by (auto simp: field_simps simp flip: power_add)
      have 01:" (\<Sum>l = 0..<n. (numbers ! j * \<omega> ^ (l * j) * \<mu> ^ (i * l))) = 
                (\<Sum>l = 0..<n. (numbers ! j *  (\<omega>^l)^(j-i))) " 
           apply(rule sum_eq) subgoal for l
           using mu_properties(1) 00[of "\<omega>^l" "\<mu>^l" "numbers ! j "] algebra_simps(23) 
           by (smt (z3) "00" left_right_inverse_power mult.assoc mult.commute mult.right_neutral power_mult)
         done
      moreover have 02:"(\<Sum>l = 0..<n. (numbers ! j *   (\<omega>^l)^(j-i)))  = 
                         numbers ! j *(\<Sum>l = 0..<n. ( (\<omega>^l)^(j-i))) " 
        by (simp add: mult_hom.hom_sum)
      moreover have 03:"(\<Sum>l = 0..<n. ( (\<omega>^l)^(j-i))) = 
                     (\<Sum>l = 0..<n. (( (\<omega>^(j-i))^l))) "
        by(rule sum_eq) (metis mult.commute power_mult)
      have "\<omega>^(j-i) \<noteq> 1"
      proof
        assume " \<omega> ^ (j - i) = 1"
        hence "ord p (to_int_mod_ring  \<omega>) \<le> j-i" using ord_max[of "j-i" \<omega>] ij_Assm by simp
        moreover have "ord p (to_int_mod_ring \<omega>) =p-1" 
          by (meson \<open>\<omega> ^ (j - i) = 1\<close> diff_is_0_eq diff_le_self ij_Assm leD le_trans omega_properties(3))
        ultimately show False 
          by (meson \<open>\<omega> ^ (j - i) = 1\<close> diff_is_0_eq diff_le_self ij_Assm leD le_trans omega_properties(3))
      qed

      text \<open>Geometric sum.\<close>

      ultimately have "(1-\<omega>^(j-i))* (\<Sum>l = 0..<n. ((\<omega>^(j-i))^l)) = (1-(\<omega>^(j-i))^n)" 
        using geo_sum[of "\<omega> ^ (j-i)" n] by simp
      moreover have "(\<omega>^(j-i))^n = 1"
        by (metis (no_types) mult.commute  omega_properties(1) power_mult power_one)
      ultimately have "(\<Sum>l = 0..<n. ((\<omega>^(j-i))^l)) = 0"
        by (metis \<open>\<omega> ^ (j - i) \<noteq> 1\<close> eq_iff_diff_eq_0 no_zero_divisors)
      thus "(\<Sum>l = 0..<n. numbers ! j * \<omega> ^ (l * j) * \<mu> ^ (i * l)) = 0" using  01 02 03 by simp
    qed

    text \<open>We compose the cases $j <i$, $j = i$ and $j > i$ to a complete summation over index $j$.\<close>

    have " (\<Sum>j = 0..<i. \<Sum>l = 0..<n. numbers ! j * \<omega> ^ (l * j) * \<mu> ^ (i * l)) = 0" using jlsi by simp
    moreover have " (\<Sum>j = i..<i+1. \<Sum>l = 0..<n. numbers ! j * \<omega> ^ (l * j) * \<mu> ^ (i * l)) =  numbers ! i * (of_int_mod_ring n)" using iisj by simp
    moreover have " (\<Sum>j = (i+1)..<n. \<Sum>l = 0..<n. numbers ! j * \<omega> ^ (l * j) * \<mu> ^ (i * l)) = 0" using ilsj by simp
    ultimately have " (\<Sum>j = 0..<n. \<Sum>l = 0..<n. numbers ! j * \<omega> ^ (l * j) * \<mu> ^ (i * l)) =
                        numbers ! i * (of_int_mod_ring n)" using i_assms sum_split 
      by (smt (z3) add.commute add.left_neutral int_ops(2) less_imp_of_nat_less of_nat_add of_nat_eq_iff of_nat_less_imp_less)
    
    text \<open>Index-wise equality can be shown.\<close>
    
    thus "intt (NTT numbers) i = of_int_mod_ring (int n) * numbers ! i" using 1 2 3
      by (metis mult.commute)
  qed
  have 2: "\<And> i. i < n \<Longrightarrow> (map ((*) (of_int_mod_ring (int n))) numbers ) ! i = (of_int_mod_ring (int n)) * (numbers ! i)"
    by (simp add: n_def)

  text \<open>We relate index-wise equality to the function definition.\<close>

   show ?thesis
     apply(rule nth_equalityI)
     subgoal my_subgoal
       unfolding INTT_def NTT_def 
       apply (simp add: n_def)
       done
     subgoal for i
     using 0 1 2 n_def algebra_simps my_subgoal length_map 
     apply  auto
     done
   done
qed

text \<open>Now we prove the converse to be true:
$\mathsf{NTT}(\mathsf{INTT}(\vec{x})) = n \cdot \vec{x}$. 
The proof proceeds analogously with exchanged roles of $\omega$ and $\mu$.
\<close>

theorem inv_ntt_correct: 
  assumes n_def: "length numbers = n"
  shows "NTT (INTT numbers) = map (\<lambda> x. (of_int_mod_ring n) * x ) numbers"
proof-
  have 0:"\<And> i. i < n \<Longrightarrow> (NTT (INTT numbers)) ! i = ntt (INTT numbers) i " using n_def length_NTT
    unfolding INTT_def NTT_def intt_def by simp
  have 1:"\<And> i. i < n \<Longrightarrow>ntt (INTT numbers) i = (of_int_mod_ring n)*numbers ! i"
  proof-
    fix i
    assume i_assms:"i < n"
    hence 1:"ntt (INTT numbers) i  =
            (\<Sum>l = 0..<n. 
               (\<Sum>j = 0..<n. numbers ! j * \<mu> ^ (l * j)) * \<omega> ^ (i * l))" 
      unfolding INTT_def ntt_def intt_def using n_def length_map nth_map by simp
    hence 2:"\<dots> = (\<Sum>l = 0..<n. 
                     (\<Sum>j = 0..<n. (numbers ! j * \<mu> ^ (l * j)) * \<omega> ^ (i * l)))" using sum_in by simp
    have 3:" \<dots> =(\<Sum>j = 0..<n. 
                  (\<Sum>l = 0..<n. (numbers ! j * \<mu> ^ (l * j) * \<omega> ^ (i * l))))" using sum_swap by fast
    have iisj:"\<And> j. j = i \<Longrightarrow> (\<Sum>l = 0..<n. (numbers ! j * \<mu> ^ (l * j) * \<omega> ^ (i * l))) = (numbers ! j)* (of_int_mod_ring n)"
    proof-
      fix j
      assume "j=i"
      hence "\<And> l. l < n \<Longrightarrow> (numbers ! j * \<mu> ^ (l * j) * \<omega> ^ (i * l))= (numbers ! j)"
        by (simp add: left_right_inverse_power mult.commute mu_properties(1))
      moreover have "\<And> l. l < n  \<Longrightarrow> numbers ! j *  \<mu> ^ (l * j) * \<omega> ^ (i * l) = numbers ! j" 
        using calculation by blast
      ultimately show "(\<Sum>l = 0..<n. (numbers ! j * \<mu> ^ (l * j) * \<omega> ^ (i * l))) = (numbers ! j)* (of_int_mod_ring n)" 
        using n_def sum_const[of "numbers ! j" n] exp_rule[of \<omega> \<mu>] mu_properties(1) 
        by (metis (no_types, lifting) atLeastLessThan_iff mult.commute sum.cong) 
    qed
    have jlsi:"\<And> j. j < i \<Longrightarrow> (\<Sum>l = 0..<n. (numbers ! j * \<mu> ^ (l * j) * \<omega> ^ (i * l))) = 0"
    proof-
      fix j
      assume j_assms:"j < i"
      hence 00:"\<And>  (c::('a::prime_card) mod_ring) a b. c * a^j*b^i  = (a*b)^j*(c * b^(i-j))" 
         using  algebra_simps 
         by (smt (z3) le_less ordered_cancel_comm_monoid_diff_class.add_diff_inverse power_add)
      have 01:" (\<Sum>l = 0..<n. (numbers ! j * \<mu> ^ (l * j) * \<omega> ^ (i * l))) = 
                (\<Sum>l = 0..<n. (numbers ! j *  (\<omega>^l)^(i-j))) " 
           apply(rule sum_eq)
           using mu_properties(1) 00 algebra_simps(23)
           by (smt (z3) mult.commute mult.left_neutral power_mult power_one)
      moreover have 02: "\<dots>=  numbers ! j *(\<Sum>l = 0..<n. ((\<omega>^l)^(i-j))) "
           using sum_in[of "\<lambda> l. numbers ! j * (\<mu> ^ l) ^ (i - j)" " numbers ! j" n] 
        by (simp add: mult_hom.hom_sum)
      moreover have 03:"(\<Sum>l = 0..<n. ((\<omega>^l)^(i-j))) = 
                     (\<Sum>l = 0..<n. ((\<omega>^(i-j))^l)) "
        by(rule sum_eq) (metis mult.commute power_mult)
      have "\<omega>^(i-j) \<noteq> 1" 
      proof
        assume "\<omega> ^ (i - j) = 1"
        hence "ord p (to_int_mod_ring \<omega>) \<le> i-j" 
          by (simp add: j_assms not_le ord_max)
         moreover have "ord p (to_int_mod_ring \<omega>) = n" using omega_properties n_lst2 unfolding ord_def
           by (meson \<open>\<omega> ^ (i - j) = 1\<close> diff_is_0_eq diff_le_self i_assms j_assms leD le_trans)
         ultimately show False 
           by (metis i_assms leD less_imp_diff_less)
      qed
      ultimately have "(1-\<omega>^(i-j))*(\<Sum>l = 0..<n. ((\<omega>^(i-j))^l)) = (1-(\<omega>^(i-j))^n)" 
        using geo_sum[of "\<omega> ^ (i - j)" n] by simp
      moreover have "(\<omega>^(i-j))^n = 1"
        by (metis (no_types)  mult.commute omega_properties(1) power_mult power_one)
      ultimately have "(\<Sum>l = 0..<n. ((\<omega>^(i-j))^l)) = 0" 
        by (metis \<open>\<omega> ^ (i - j) \<noteq> 1\<close> divisors_zero eq_iff_diff_eq_0)
      thus "(\<Sum>l = 0..<n. numbers ! j * \<mu> ^ (l * j) * \<omega> ^ (i * l)) = 0" using  01 02 03 by simp
    qed
    have ilsj:"\<And> j. i < j \<and> j < n \<Longrightarrow> (\<Sum>l = 0..<n. (numbers ! j * \<mu> ^ (l * j) * \<omega> ^ (i * l))) = 0"
    proof-
      fix j
      assume ij_Assm: "i < j \<and> j < n"
      hence 00:"\<And>  (c::('a::prime_card) mod_ring) a b. (a*b)^i*(c * b^(j-i)) = c * a^i*b^j  " 
        by (simp add: field_simps flip: power_add)
      have 01:" (\<Sum>l = 0..<n. (numbers ! j * \<mu> ^ (l * j) * \<omega> ^ (i * l))) = 
                (\<Sum>l = 0..<n. (numbers ! j *  (\<mu>^l)^(j-i))) " 
           apply(rule sum_eq) subgoal for l
           using mu_properties(1) 00[of "\<omega>^l" "\<mu>^l" "numbers ! j "] algebra_simps(23) 
           by (smt (z3) "00" left_right_inverse_power mult.assoc mult.commute mult.right_neutral power_mult)
         done
      moreover have 02:"(\<Sum>l = 0..<n. (numbers ! j *   (\<mu>^l)^(j-i)))  = 
            numbers ! j *(\<Sum>l = 0..<n. ( (\<mu>^l)^(j-i))) " 
        by (simp add: mult_hom.hom_sum)
      moreover have 03:"(\<Sum>l = 0..<n. ( (\<mu>^l)^(j-i))) = 
                     (\<Sum>l = 0..<n. (( (\<mu>^(j-i))^l))) "
        by(rule sum_eq) (metis mult.commute power_mult)
      have "\<mu>^(j-i) \<noteq> 1"
       proof
        assume "\<mu> ^ (j - i) = 1"
        hence "ord p (to_int_mod_ring \<mu>) \<le> j -i " 
          by (simp add: ij_Assm not_le ord_max)
        moreover hence "ord p (to_int_mod_ring \<omega>) \<le> j-i" 
          by (metis \<open>\<mu> ^ (j - i) = 1\<close> diff_is_0_eq exp_rule ij_Assm leD mult.comm_neutral mult.commute mu_properties(1) ord_max)
        moreover hence "j-i < n" using ij_Assm i_assms p_fact k_bound n_lst2 by linarith
        moreover have "ord p (to_int_mod_ring \<omega>) = n" using omega_properties n_lst2 unfolding ord_def
          by (metis (no_types) \<open>\<mu> ^ (j-i) = 1\<close> calculation(3) diff_is_0_eq ij_Assm leD left_right_inverse_power mult.comm_neutral mult_cancel_left mu_properties(1) omega_properties(3) zero_neq_one)
        ultimately show False by simp
      qed
      ultimately have "(1-\<mu>^(j-i))* (\<Sum>l = 0..<n. ((\<mu>^(j-i))^l)) = (1-(\<mu>^(j-i))^n)" 
        using geo_sum[of "\<mu> ^ (j-i)" n] by simp
      moreover have "(\<mu>^(j-i))^n = 1"
        by (metis (no_types) left_right_inverse_power mult.commute mult.right_neutral mu_properties(1) omega_properties(1) power_mult power_one)
      ultimately have "(\<Sum>l = 0..<n. ((\<mu>^(j-i))^l)) = 0"
        by (metis \<open>\<mu> ^ (j - i) \<noteq> 1\<close> eq_iff_diff_eq_0 no_zero_divisors)
      thus "(\<Sum>l = 0..<n. numbers ! j * \<mu> ^ (l * j) * \<omega> ^ (i * l)) = 0" using  01 02 03 by simp
    qed
    have " (\<Sum>j = 0..<i. \<Sum>l = 0..<n. numbers ! j * \<mu> ^ (l * j) * \<omega> ^ (i * l)) = 0" using jlsi by simp
    moreover have " (\<Sum>j = i..<i+1. \<Sum>l = 0..<n. numbers ! j * \<mu> ^ (l * j) * \<omega> ^ (i * l)) =  numbers ! i * (of_int_mod_ring n)" using iisj by simp
    moreover have " (\<Sum>j = (i+1)..<n. \<Sum>l = 0..<n. numbers ! j * \<mu> ^ (l * j) * \<omega> ^ (i * l)) = 0" using ilsj by simp
    ultimately have " (\<Sum>j = 0..<n. \<Sum>l = 0..<n. numbers ! j * \<mu> ^ (l * j) * \<omega> ^ (i * l)) =
                        numbers ! i * (of_int_mod_ring n)" using i_assms sum_split 
      by (smt (z3) add.commute add.left_neutral int_ops(2) less_imp_of_nat_less of_nat_add of_nat_eq_iff of_nat_less_imp_less)
    thus "ntt (INTT numbers) i = of_int_mod_ring (int n) * numbers ! i" using 1 2 3 
      by (metis mult.commute)
  qed
  have 2: "\<And> i. i < n \<Longrightarrow> (map ((*) (of_int_mod_ring (int n))) numbers ) ! i = (of_int_mod_ring (int n)) * (numbers ! i)"
     by (simp add: n_def)
   show ?thesis
     apply(rule nth_equalityI)
     subgoal my_little_subgoal
       unfolding INTT_def NTT_def 
       apply (simp add: n_def)
       done
     subgoal for i
       using 0 1 2 n_def algebra_simps  my_little_subgoal length_map 
       apply  auto
     done
   done
qed

end
end
