theory MTF_pairwise
imports List_Factoring
MTF_2comp_on2
begin


(* "(posxy qs {x, y} (Suc n + nextxy {x, y} (drop (Suc n) qs)))
                  = Suc (posxy qs {x, y} (n + nextxy {x, y} (drop n qs)))"
*)

fun nthxy where
  "nthxy S [] n = 0"
| "nthxy S (x#xs) 0 = (if x\<in>S then 0 else 1 + nthxy S xs 0)"
| "nthxy S (x#xs) (Suc n) = (if x\<in>S then nthxy S xs n else 1 + nthxy S xs (Suc n))"

lemma "S \<inter> set xs = {} \<Longrightarrow> nthxy S xs i = length xs"
proof (induct xs)
  case (Cons x xs)
  then have "x \<notin> S" by auto
  with Cons show ?case apply(auto) apply(cases i) by(simp_all)
qed simp
 

term "find_index"
definition "nextxy S xs = find_index (\<lambda>x. x\<in>S) xs"
definition "lastxy S xs = 
  (let i = nextxy S (rev xs); n = size xs
    in if i = n then i else n - (i+1))"

lemma lastxy_index_le_size: "lastxy S qs \<le> length qs"
unfolding lastxy_def by auto

lemma "xs!lastxy S xs \<in> S"
unfolding lastxy_def nextxy_def apply(simp) oops



theorem MTF_pairwise: "pairwise (embed MTF)"
proof(rule pairwise_property_lemma)
  case (goal1 init qs x y)
  then have xyininit: "{x, y} \<subseteq> set init" 
        and qsininit: "set qs \<subseteq> set init" by auto
  have dinit: "distinct init" sorry
  from goal1 have xny: "x\<noteq>y" by simp

  from qsininit show ?case 
    proof (induct qs rule: rev_induct)
      case Nil 
      show ?case unfolding Pbefore_in_def MTF_def
        apply(simp)
        apply(rule Lxy_mono)
          apply(fact xyininit)
          by(fact dinit)
    next
      case (snoc q qs)
      then have iH: "Pbefore_in x y (embed MTF) qs init =
        Pbefore_in x y (embed MTF) (Lxy qs {x, y}) (Lxy init {x, y})" by auto 

      thm bind_return_pmf map_bind_pmf
      have "Pbefore_in x y (embed MTF) (qs@[q]) init 
         = bind_pmf (config_rand (embed MTF) init qs)
              (\<lambda>xa. return_pmf (x < y in mtf2 (length (fst xa) - 1) (q) (fst xa)))"
            unfolding Pbefore_in_def MTF_def
         by (auto simp add: config'_rand_snoc map_pmf_def bind_assoc_pmf take_Suc_conv_app_nth  bind_return_pmf map_bind_pmf split_def step_def)
      also have "\<dots> = map_pmf (\<lambda>xa. (x < y in mtf2 (length (fst xa) - 1) (q) (fst xa)))
              (config_rand (embed MTF) init qs)" unfolding map_pmf_def by simp
      also have "\<dots> = map_pmf (\<lambda>p. x < y in fst p)
                      (config_rand (embed MTF) (Lxy init {x, y}) (Lxy (qs@[q]) {x, y}) )"
      proof (cases "q \<in> {x,y}")
        case True                                            

        have "map_pmf (\<lambda>xa. x < y in mtf2 (length (fst xa) -1) (q) (fst xa))
                      (config_rand (embed MTF) init qs)
           =  map_pmf (\<lambda>xa. (x < y in mtf2 (length (fst xa) -1) q (fst xa)))
                      (config_rand (embed MTF) (Lxy init {x, y}) (Lxy qs {x, y}))
              "
        proof (cases "q=x")
          case True

          have " map_pmf (\<lambda>xa. x < y in mtf2 (length (fst xa) -1) (q) (fst xa))
                          (config_rand (embed MTF) init qs)
              =  map_pmf (\<lambda>xa. True) (config_rand (embed MTF) init qs)"
            unfolding True
              proof (rule pmf.map_cong0)
                case (goal1 z)
                then have 1: "distinct (fst z)" using config_rand_distinct dinit by metis
                have "set (fst z) = set init" using goal1 config_rand_set by metis
                then have 2: "x \<in> set (fst z)" "y \<in> set (fst z)"
                      using xyininit by auto                  
                from 1 2 xny show ?case using mtf2_moves_to_front' by metis  
              qed
          also have "\<dots> = return_pmf True" by auto
          also have "\<dots> = map_pmf (\<lambda>xa. True)
                                  (config_rand (embed MTF) (Lxy init {x, y}) (Lxy qs {x, y}))"
                                  by auto
          also have "\<dots> = map_pmf
            (\<lambda>xa. x < y in mtf2 (length (fst xa) -1) q (fst xa))
              (config_rand (embed MTF) (Lxy init {x, y}) (Lxy qs {x, y}))" unfolding True
                proof (rule pmf.map_cong0)
                  case goal1
                  then have 1: "distinct (fst z)" using config_rand_distinct dinit Lxy_distinct by metis
                  have "set (fst z) = set (Lxy init {x, y})" using goal1 config_rand_set by metis
                  also have "\<dots> = {x,y}" using  xyininit by (simp add: Lxy_set_filter)
                  finally have 2: "x\<in>set (fst z)" "y\<in>set (fst z)" by auto
                  from 1 2 xny show ?case using mtf2_moves_to_front' by metis  
                qed
          finally show ?thesis .
        next



          case False
          with True have yreq: "q=y" by simp
          have "map_pmf (\<lambda>xa. x < y in mtf2 (length (fst xa) -1) (q) (fst xa))
                  (config_rand (embed MTF) init qs)
                   =  map_pmf (\<lambda>xa. False) (config_rand (embed MTF) init qs)"
            unfolding yreq
            proof (rule pmf.map_cong0)
              case goal1
              then have 1: "distinct (fst z)" using config_rand_distinct dinit by metis
              have "set (fst z) = set init" using goal1 config_rand_set by metis
              then have 2: "x \<in> set (fst z)" "y \<in> set (fst z)"
                    using xyininit by auto                   
              from 1 2 xny have "y < x in mtf2 (length (fst z)-1) y (fst z) = True"
                  using mtf2_moves_to_front' by metis  
              then show ?case using xny 2 by simp
            qed
          also have "\<dots> = return_pmf False" by auto
          also have "\<dots> = map_pmf (\<lambda>xa. False) (config_rand (embed MTF) 
                    (Lxy init {x, y}) (Lxy qs {x, y}))" by auto
          also have "\<dots> = map_pmf (\<lambda>xa. x < y in mtf2 (length (fst xa) -1) q (fst xa))
                    (config_rand (embed MTF)
                    (Lxy init {x, y}) (Lxy qs {x, y}))" unfolding yreq
            proof (rule pmf.map_cong0)
              case goal1
              then have 1: "distinct (fst z)" using config_rand_distinct dinit Lxy_distinct by metis
              have "set (fst z) = set (Lxy init {x, y})" using goal1 config_rand_set by metis
              also have "\<dots> = {x,y}" using  xyininit by (simp add: Lxy_set_filter)
              finally have 2: "x\<in>set (fst z)" "y\<in>set (fst z)" by auto
              from 1 2 xny have "y < x in mtf2 (length (fst z)-1) y (fst z) = True"
                  using mtf2_moves_to_front' by metis  
              then show ?case using xny 2 by simp  
            qed
          finally show ?thesis .         
        qed
        also have "\<dots> =  bind_pmf (config_rand (embed MTF)
              (Lxy init {x, y}) (Lxy qs {x, y}))
              (\<lambda>xa. return_pmf (x < y in mtf2 (length (fst xa) -1) q
                (fst xa)))"
                unfolding map_pmf_def by simp 
        also have "\<dots> = 
              map_pmf (\<lambda>p. x < y in fst p)
                (config_rand (embed MTF)(Lxy init {x, y}) (Lxy (qs@[q]) {x, y}) )"
                  using True apply(simp add: Lxy_snoc)
                  by(simp add: MTF_def config'_rand_snoc bind_return_pmf map_bind_pmf step_def)
  
        finally show ?thesis .
      next


        case False 

        have "map_pmf (\<lambda>xa. x < y in mtf2 (length (fst xa) -1) (q) (fst xa))
                (config_rand (embed MTF) init qs)
            = map_pmf (\<lambda>p. x < y in fst p)
                (config_rand (embed MTF) init qs)" 
             proof(rule pmf.map_cong0)
                case goal1
                from False have 1: "q\<noteq>x" "q\<noteq>y" by auto
                have 2: "distinct (fst z)" using goal1 config_rand_distinct dinit by (metis)
                have "set (fst z) = set init" using goal1 config_rand_set by metis
                then have 3: "x \<in> set (fst z)" "y \<in> set (fst z)" "q \<in> set (fst z)"
                      using xyininit snoc(2) by auto                  
                from 1 2 3 show ?case by (metis xy_relativorder_mtf2)
             qed
        also have "\<dots> =
              map_pmf (\<lambda>p. x < y in fst p)
                (config_rand (embed MTF) (Lxy init {x, y}) (Lxy qs {x, y}) )"
                  using iH[unfolded Pbefore_in_def ] by auto
        also have "\<dots> = 
              map_pmf (\<lambda>p. x < y in fst p)
                (config_rand (embed MTF) (Lxy init {x, y}) (Lxy (qs@[q]) {x, y}))" using False by(simp add: Lxy_snoc)
        finally show ?thesis .
      qed
      also have "\<dots> = Pbefore_in x y (embed MTF) (Lxy (qs@[q]) {x, y}) (Lxy init {x, y}) "
                   unfolding Pbefore_in_def MTF_def by simp
      finally show ?case .
    qed  
qed (simp add: MTF_def)


lemma MTF_has_finite_config_set: "(\<And>init qs x.
    distinct init \<Longrightarrow>
    set qs \<subseteq> set init \<Longrightarrow>
    x < length qs \<Longrightarrow>
    finite (set_pmf (config'' (embed MTF) qs init x)))"
proof -
  case goal1
  from goal1(1,3) show ?case
  apply (induct x)
    apply(simp add: MTF_def) 
    by (simp add: take_Suc_conv_app_nth config'_rand_snoc split_def  )
qed


thm MTF_OPT2


theorem MTF2: "(x::nat) \<noteq> y \<Longrightarrow> set qs \<subseteq> {x,y}
     \<Longrightarrow> T\<^sub>p_on MTF  [x, y] qs \<le> 2 * (T\<^sub>p_opt [x,y] qs) + 2"
proof -
  case goal1
  with OPT2_is_opt[OF goal1(2) goal1(1)] have a: "T\<^sub>p [x, y] qs (OPT2 qs [x, y]) = T\<^sub>p_opt [x,y] qs" by simp
  show ?case unfolding a[symmetric]
    apply(rule MTF_OPT2[of x y qs])
    by(auto simp: goal1)
qed



thm MTF2 T_on_embed  
 
theorem MTF2_embd: assumes "(x::nat) \<noteq> y" and "set qs \<subseteq> {x,y}"
  shows
    "T\<^sub>p_on_rand (embed MTF)  [x, y] qs \<le> 2 * (T\<^sub>p_opt [x,y] qs) + 2"
proof -
  have "T\<^sub>p_on_rand (embed MTF)  [x, y] qs
        = T\<^sub>p_on MTF  [x, y] qs" by(simp only: T_on_embed)
  also have "\<dots> \<le>  2 * (T\<^sub>p_opt [x,y] qs) + 2"
    using MTF2[OF assms] by simp
  finally show ?thesis .
qed



theorem MTF_2_competitive_again: "\<forall>s0\<in>{x::nat list. distinct x \<and> x\<noteq>[]}.
   \<exists>b\<ge>0. \<forall>qs\<in>{x. set x \<subseteq> set s0}.
             T\<^sub>p_on_rand (embed MTF) s0 qs \<le> (2::real) *  T\<^sub>p_opt s0 qs + b"
unfolding MTF_def
proof(rule factoringlemma_withconstant)
  case goal5
  show ?case 
    proof (safe)
      case (goal1 init)
      note out=this
      show ?case
        apply(rule exI[where x=2])
          apply(simp)
          proof (safe)
            case (goal1 qs a b)
            then have a: "a\<noteq>b" by simp
            have twist: "{a,b}={b, a}" by auto
            have b1: "set (Lxy qs {a, b}) \<subseteq> {a, b}" unfolding Lxy_def by auto
            with this[unfolded twist] have b2: "set (Lxy qs {b, a}) \<subseteq> {b, a}" by(auto)
        
            have "set (Lxy init {a, b}) = {a,b} \<inter> (set init)" apply(induct init)
                unfolding Lxy_def by(auto)
            with goal1 have A: "set (Lxy init {a, b}) = {a,b}" by auto
            have "finite {a,b}" by auto
            from out have B: "distinct (Lxy init {a, b})" unfolding Lxy_def by auto
            have C: "length (Lxy init {a, b}) = 2"
              using distinct_card[OF B, unfolded A] using a by auto
        
            have "{xs. set xs = {a,b} \<and> distinct xs \<and> length xs =(2::nat)} 
                    = { [a,b], [b,a] }"
                  apply(auto simp: a a[symmetric])
                  proof -
                    case (goal1 xs)
                    from goal1(4) obtain x xs' where r:"xs=x#xs'" by (metis Suc_length_conv add_2_eq_Suc' append_Nil length_append)
                    with goal1(4) have "length xs' = 1" by auto
                    then obtain y where s: "[y] = xs'" by (metis One_nat_def length_0_conv length_Suc_conv)
                    from r s have t: "[x,y] = xs" by auto
                    moreover from t goal1(1) have "x=b" using doubleton_eq_iff goal1(2) by fastforce
                    moreover from t goal1(1) have "y=a" using doubleton_eq_iff goal1(2) by fastforce
                    ultimately show ?case by auto
                  qed
        
            with A B C have pos: "(Lxy init {a, b}) = [a,b]
                  \<or> (Lxy init {a, b}) = [b,a]" by auto
            
            show ?case
              apply(cases "(Lxy init {a, b}) = [a,b]")  
                apply(simp) using MTF2_embd[OF a b1, unfolded MTF_def] apply(simp)
                using pos apply(simp) unfolding twist 
              using MTF2_embd[OF a[symmetric] b2, unfolded MTF_def] by(simp)
          qed
    qed
next
  case goal4  then show ?case using MTF_pairwise[unfolded MTF_def] by simp
next
  case goal7 then show ?case using MTF_has_finite_config_set[unfolded MTF_def] by simp
qed (simp_all)


end