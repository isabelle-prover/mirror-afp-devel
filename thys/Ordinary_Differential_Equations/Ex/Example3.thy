theory Example3
imports
  "../Numerics/Euler_Affine"
  "../Numerics/Optimize_Float"
  "~~/src/HOL/Decision_Procs/Approximation"
begin

subsection \<open>Example 3\<close>

approximate_affine e3 "\<lambda>(t, x). (1::real, x*x + t*t::real)"

lemma e3_fderiv: "((\<lambda>(t, x). (1::real, x*x + t*t::real)) has_derivative
  (\<lambda>(x, y) (h, j). (0, 2 * (j * y) + 2 * (h * x))) x) (at x within X)"
       by (auto intro!: derivative_eq_intros simp: split_beta')

approximate_affine e3_d "\<lambda>(x, y) (h, j). (0::real, 2 * (j * y) + 2 * (h * x)::real)"

abbreviation "e3_ivp \<equiv> \<lambda>optns args. uncurry_options e3 optns (hd args) (tl args)"
abbreviation "e3_d_ivp \<equiv> \<lambda>optns args. uncurry_options e3_d optns (hd args) (hd (tl args)) (tl (tl args))"

interpretation e3: aform_approximate_ivp
  e3_ivp
  e3_d_ivp
  "\<lambda>(t, x). (1::real, x*x + t*t::real)"
  "\<lambda>(x, y) (h, j). (0, 2 * (j * y) + 2 * (h * x))"
  apply unfold_locales
  apply (rule e3[THEN Joints2_JointsI])
  unfolding list.sel apply assumption apply assumption
  apply (drule length_set_of_apprs, simp)\<comment>"TODO: prove in affine-approximation"
  apply (rule e3_fderiv)
  apply (rule e3_d[THEN Joints2_JointsI]) apply assumption apply assumption
  apply (drule length_set_of_apprs, simp)\<comment>"TODO: prove in affine-approximation"
  apply (auto intro!: continuous_intros simp: split_beta')
  done

definition "e3_optns = default_optns
    \<lparr> precision := 30,
      tolerance := FloatR 1 (- 4),
      stepsize  := FloatR 1 (- 8),
      result_fun := ivls_result 23 1,
      printing_fun := (\<lambda>_ _ _. ())\<rparr>"

definition "e3test = (\<lambda>_::unit. euler_series_result e3_ivp e3_d_ivp e3_optns 0 (aform_of_point (0, 1)) (2 ^ 5))"

lemma e3test: "e3test () =
  Some (FloatR 32 (- 8),
       [(FloatR 31 (- 8), (FloatR 62 (- 9), FloatR 9549658 (- 23)), (FloatR 64 (- 9), FloatR 9592906 (- 23)),
         FloatR 32 (- 8), (FloatR 32 (- 8), FloatR 9592812 (- 23)), FloatR 32 (- 8), FloatR 9592906 (- 23)),
        (FloatR 30 (- 8), (FloatR 60 (- 9), FloatR 9506917 (- 23)), (FloatR 62 (- 9), FloatR 9549748 (- 23)),
         FloatR 31 (- 8), (FloatR 31 (- 8), FloatR 9549658 (- 23)), FloatR 31 (- 8), FloatR 9549748 (- 23)),
        (FloatR 29 (- 8), (FloatR 58 (- 9), FloatR 9464583 (- 23)), (FloatR 60 (- 9), FloatR 9507004 (- 23)),
         FloatR 30 (- 8), (FloatR 30 (- 8), FloatR 9506918 (- 23)), FloatR 30 (- 8), FloatR 9507004 (- 23)),
        (FloatR 28 (- 8), (FloatR 56 (- 9), FloatR 9422650 (- 23)), (FloatR 58 (- 9), FloatR 9464666 (- 23)),
         FloatR 29 (- 8), (FloatR 29 (- 8), FloatR 9464584 (- 23)), FloatR 29 (- 8), FloatR 9464666 (- 23)),
        (FloatR 27 (- 8), (FloatR 54 (- 9), FloatR 9381111 (- 23)), (FloatR 56 (- 9), FloatR 9422729 (- 23)),
         FloatR 28 (- 8), (FloatR 28 (- 8), FloatR 9422650 (- 23)), FloatR 28 (- 8), FloatR 9422729 (- 23)),
        (FloatR 26 (- 8), (FloatR 52 (- 9), FloatR 9339960 (- 23)), (FloatR 54 (- 9), FloatR 9381186 (- 23)),
         FloatR 27 (- 8), (FloatR 27 (- 8), FloatR 9381111 (- 23)), FloatR 27 (- 8), FloatR 9381186 (- 23)),
        (FloatR 25 (- 8), (FloatR 50 (- 9), FloatR 9299191 (- 23)), (FloatR 52 (- 9), FloatR 9340031 (- 23)),
         FloatR 26 (- 8), (FloatR 26 (- 8), FloatR 9339960 (- 23)), FloatR 26 (- 8), FloatR 9340031 (- 23)),
        (FloatR 24 (- 8), (FloatR 48 (- 9), FloatR 9258799 (- 23)), (FloatR 50 (- 9), FloatR 9299259 (- 23)),
         FloatR 25 (- 8), (FloatR 25 (- 8), FloatR 9299191 (- 23)), FloatR 25 (- 8), FloatR 9299259 (- 23)),
        (FloatR 23 (- 8), (FloatR 46 (- 9), FloatR 9218777 (- 23)), (FloatR 48 (- 9), FloatR 9258863 (- 23)),
         FloatR 24 (- 8), (FloatR 24 (- 8), FloatR 9258799 (- 23)), FloatR 24 (- 8), FloatR 9258863 (- 23)),
        (FloatR 22 (- 8), (FloatR 44 (- 9), FloatR 9179120 (- 23)), (FloatR 46 (- 9), FloatR 9218838 (- 23)),
         FloatR 23 (- 8), (FloatR 23 (- 8), FloatR 9218777 (- 23)), FloatR 23 (- 8), FloatR 9218838 (- 23)),
        (FloatR 21 (- 8), (FloatR 42 (- 9), FloatR 9139823 (- 23)), (FloatR 44 (- 9), FloatR 9179178 (- 23)),
         FloatR 22 (- 8), (FloatR 22 (- 8), FloatR 9179121 (- 23)), FloatR 22 (- 8), FloatR 9179178 (- 23)),
        (FloatR 20 (- 8), (FloatR 40 (- 9), FloatR 9100880 (- 23)), (FloatR 42 (- 9), FloatR 9139878 (- 23)),
         FloatR 21 (- 8), (FloatR 21 (- 8), FloatR 9139824 (- 23)), FloatR 21 (- 8), FloatR 9139878 (- 23)),
        (FloatR 19 (- 8), (FloatR 38 (- 9), FloatR 9062286 (- 23)), (FloatR 40 (- 9), FloatR 9100932 (- 23)),
         FloatR 20 (- 8), (FloatR 20 (- 8), FloatR 9100880 (- 23)), FloatR 20 (- 8), FloatR 9100932 (- 23)),
        (FloatR 18 (- 8), (FloatR 36 (- 9), FloatR 9024034 (- 23)), (FloatR 38 (- 9), FloatR 9062334 (- 23)),
         FloatR 19 (- 8), (FloatR 19 (- 8), FloatR 9062286 (- 23)), FloatR 19 (- 8), FloatR 9062334 (- 23)),
        (FloatR 17 (- 8), (FloatR 34 (- 9), FloatR 8986121 (- 23)), (FloatR 36 (- 9), FloatR 9024080 (- 23)),
         FloatR 18 (- 8), (FloatR 18 (- 8), FloatR 9024035 (- 23)), FloatR 18 (- 8), FloatR 9024080 (- 23)),
        (FloatR 16 (- 8), (FloatR 32 (- 9), FloatR 8948541 (- 23)), (FloatR 34 (- 9), FloatR 8986164 (- 23)),
         FloatR 17 (- 8), (FloatR 17 (- 8), FloatR 8986121 (- 23)), FloatR 17 (- 8), FloatR 8986164 (- 23)),
        (FloatR 15 (- 8), (FloatR 30 (- 9), FloatR 8911288 (- 23)), (FloatR 32 (- 9), FloatR 8948580 (- 23)),
         FloatR 16 (- 8), (FloatR 16 (- 8), FloatR 8948541 (- 23)), FloatR 16 (- 8), FloatR 8948580 (- 23)),
        (FloatR 14 (- 8), (FloatR 28 (- 9), FloatR 8874358 (- 23)), (FloatR 30 (- 9), FloatR 8911325 (- 23)),
         FloatR 15 (- 8), (FloatR 15 (- 8), FloatR 8911288 (- 23)), FloatR 15 (- 8), FloatR 8911325 (- 23)),
        (FloatR 13 (- 8), (FloatR 26 (- 9), FloatR 8837747 (- 23)), (FloatR 28 (- 9), FloatR 8874392 (- 23)),
         FloatR 14 (- 8), (FloatR 14 (- 8), FloatR 8874359 (- 23)), FloatR 14 (- 8), FloatR 8874392 (- 23)),
        (FloatR 12 (- 8), (FloatR 24 (- 9), FloatR 8801448 (- 23)), (FloatR 26 (- 9), FloatR 8837778 (- 23)),
         FloatR 13 (- 8), (FloatR 13 (- 8), FloatR 8837747 (- 23)), FloatR 13 (- 8), FloatR 8837778 (- 23)),
        (FloatR 11 (- 8), (FloatR 22 (- 9), FloatR 8765457 (- 23)), (FloatR 24 (- 9), FloatR 8801476 (- 23)),
         FloatR 12 (- 8), (FloatR 12 (- 8), FloatR 8801448 (- 23)), FloatR 12 (- 8), FloatR 8801476 (- 23)),
        (FloatR 10 (- 8), (FloatR 20 (- 9), FloatR 8729770 (- 23)), (FloatR 22 (- 9), FloatR 8765483 (- 23)),
         FloatR 11 (- 8), (FloatR 11 (- 8), FloatR 8765457 (- 23)), FloatR 11 (- 8), FloatR 8765483 (- 23)),
        (FloatR 9 (- 8), (FloatR 18 (- 9), FloatR 8694382 (- 23)), (FloatR 20 (- 9), FloatR 8729794 (- 23)),
         FloatR 10 (- 8), (FloatR 10 (- 8), FloatR 8729770 (- 23)), FloatR 10 (- 8), FloatR 8729794 (- 23)),
        (FloatR 8 (- 8), (FloatR 16 (- 9), FloatR 8659289 (- 23)), (FloatR 18 (- 9), FloatR 8694403 (- 23)),
         FloatR 9 (- 8), (FloatR 9 (- 8), FloatR 8694382 (- 23)), FloatR 9 (- 8), FloatR 8694403 (- 23)),
        (FloatR 7 (- 8), (FloatR 14 (- 9), FloatR 8624485 (- 23)), (FloatR 16 (- 9), FloatR 8659307 (- 23)),
         FloatR 8 (- 8), (FloatR 8 (- 8), FloatR 8659289 (- 23)), FloatR 8 (- 8), FloatR 8659307 (- 23)),
        (FloatR 6 (- 8), (FloatR 12 (- 9), FloatR 8589966 (- 23)), (FloatR 14 (- 9), FloatR 8624501 (- 23)),
         FloatR 7 (- 8), (FloatR 7 (- 8), FloatR 8624485 (- 23)), FloatR 7 (- 8), FloatR 8624501 (- 23)),
        (FloatR 5 (- 8), (FloatR 10 (- 9), FloatR 8555729 (- 23)), (FloatR 12 (- 9), FloatR 8589980 (- 23)),
         FloatR 6 (- 8), (FloatR 6 (- 8), FloatR 8589966 (- 23)), FloatR 6 (- 8), FloatR 8589980 (- 23)),
        (FloatR 4 (- 8), (FloatR 8 (- 9), FloatR 8521768 (- 23)), (FloatR 10 (- 9), FloatR 8555740 (- 23)),
         FloatR 5 (- 8), (FloatR 5 (- 8), FloatR 8555729 (- 23)), FloatR 5 (- 8), FloatR 8555740 (- 23)),
        (FloatR 3 (- 8), (FloatR 6 (- 9), FloatR 8488080 (- 23)), (FloatR 8 (- 9), FloatR 8521777 (- 23)),
         FloatR 4 (- 8), (FloatR 4 (- 8), FloatR 8521768 (- 23)), FloatR 4 (- 8), FloatR 8521777 (- 23)),
        (FloatR 2 (- 8), (FloatR 4 (- 9), FloatR 8454659 (- 23)), (FloatR 6 (- 9), FloatR 8488087 (- 23)),
         FloatR 3 (- 8), (FloatR 3 (- 8), FloatR 8488080 (- 23)), FloatR 3 (- 8), FloatR 8488087 (- 23)),
        (FloatR 1 (- 8), (FloatR 2 (- 9), FloatR 8421503 (- 23)), (FloatR 4 (- 9), FloatR 8454665 (- 23)),
         FloatR 2 (- 8), (FloatR 2 (- 8), FloatR 8454660 (- 23)), FloatR 2 (- 8), FloatR 8454665 (- 23)),
        (FloatR 0 0, (FloatR 0 (- 9), FloatR 8388608 (- 23)), (FloatR 2 (- 9), FloatR 8421507 (- 23)), FloatR 1 (- 8),
         (FloatR 1 (- 8), FloatR 8421503 (- 23)), FloatR 1 (- 8), FloatR 8421507 (- 23))])"
   by eval


lemma x0: "(0, 1) \<in> Affine (aform_of_point (0::real, 1::real))"
  by (rule Affine_aform_of_point)

lemma stepsize: "0 < stepsize e3_optns"
  by (auto simp: e3_optns_def)

lemma result_fun: "result_fun e3_optns = ivls_result 23 1"
  by (auto simp: e3_optns_def)

lemmas certification = e3.euler_series_ivls_result[OF stepsize x0 result_fun e3test[simplified e3test_def],
  simplified e3.euler_ivp_def]


lemma last_enclosure: "e3.enclosure
     (ivp.solution
       \<lparr>ivp_f = \<lambda>(t, x). case x of (t, x) \<Rightarrow> (1, x * x + t * t), ivp_t0 = 0, ivp_x0 = (0, 1), ivp_T = {0..FloatR 32 (- 8)},
          ivp_X = UNIV\<rparr>)
     0 (FloatR 32 (- 8))
     (map set_res_of_ivl_res
       [(FloatR 31 (- 8), (FloatR 62 (- 9), FloatR 9549658 (- 23)), (FloatR 64 (- 9), FloatR 9592906 (- 23)),
         FloatR 32 (- 8), (FloatR 32 (- 8), FloatR 9592812 (- 23)), FloatR 32 (- 8), FloatR 9592906 (- 23))])"
  using certification
  unfolding e3.enclosure_def
  apply (subst (asm) list.map)
  apply (subst (asm) list_all_simps)
  apply (drule conjunct1)
  apply (simp )
  done

lemma
  "unique_solution \<lparr>ivp_f = \<lambda>(s::real, t::real, x::real). (1, x * x + t * t), ivp_t0 = 0,
    ivp_x0 = (0, 1), ivp_T = {0..1 / 8}, ivp_X = UNIV\<rparr>"
  "ivp.solution    \<lparr>ivp_f = \<lambda>(s::real, t::real, x::real). (1, x * x + t * t), ivp_t0 = 0,
    ivp_x0 = (0, 1), ivp_T = {0..1 / 8}, ivp_X = UNIV\<rparr> (1 / 8) \<in>
    {(1 / 8, 2398203 / 2097152) .. (1 / 8, 4796453 / 4194304)}"
  using certification(1) last_enclosure
  by (simp_all add: e3.enclosure_def)

subsubsection \<open>Comparison with bounds analytically obtained by Walter~\cite{walter} in section 9,
  Example V.\<close>

text \<open>First approximation.\<close>

notepad begin
  fix solution
  assume Walter: "\<And>x. solution x \<in> {1/(1 - x)..tan(x + pi/4)}"
  let ?x = "0.125::real"
  value "1 / (1 - 0.125)"
  have "1/(1-?x) \<in> {1.142857139 .. 1.142857146}" by simp
  moreover
  approximate "tan (0.125 + pi/4)"
  have "tan(?x + pi/4) \<in> {1.287426935 .. 1.287426955}"
    by (approximation 40)
  ultimately
  have "{1/(1-?x)..tan(?x + pi/4)} \<subseteq> {1.142857139 .. 1.287426955}" by simp
  with Walter have "solution ?x \<in> {1.142857139 .. 1.287426955}" by blast
end

text \<open>Better approximation.\<close>

notepad begin
  fix solution::"real\<Rightarrow>real"
  assume Walter: "\<And>x. solution x \<in> {1/(1-x)..16 / (16 - 17*x)}"
  let ?x = "0.125::real"
  approximate "1 / (1 - ?x)"
  have "1/(1-?x) \<in> {1.142857139 .. 1.142857146}" by simp
  moreover
  approximate "16 / (16 - 17*?x)"
  have "16 / (16 - 17*?x) \<in> {1.153153151 .. 1.153153155}"
    by (approximation 40)
  ultimately
  have "{1/(1-?x)..16 / (16 - 17*?x)} \<subseteq> {1.142857139 .. 1.153153155}" by simp
  with Walter have "solution ?x \<in> {1.142857139 .. 1.153153155}" by blast
  have error: "16 / (16 - 17*?x) - 1 / (1 - ?x) \<ge> 1/10^2" by (approximation 20)
end

end
