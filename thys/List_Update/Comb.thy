theory Comb
imports TS BIT_2comp_on2 BIT_pairwise
begin


(*  state of BIT: bool list     bit string
    state of TS: nat list       history
*)




datatype CombState = CBit "bool list * nat list" | CTs "nat list" 
                          
fun COMB_init :: "nat list \<Rightarrow> (nat state, CombState) alg_on_init" where
  "COMB_init h init = do {
                    (b::bool) \<leftarrow> (bernoulli_pmf 0.8);
                    (xs::bool list) \<leftarrow> Prob_Theory.bv (length init);
                    return_pmf (if b then CBit (xs, init) else CTs h)
                  }"
  
definition COMB_step :: "(nat state, CombState, nat, answer) alg_on_step" where
"COMB_step s q = (case snd s of CBit b \<Rightarrow> map_pmf (\<lambda>((a,b),c). ((a,b),CBit c)) (BIT_step (fst s, b) q)
                              | CTs b \<Rightarrow> map_pmf (\<lambda>((a,b),c). ((a,b),CTs c)) (return_pmf (TS_step_d (fst s, b) q)))"
            
definition "COMB h = (COMB_init h, COMB_step)"

term "config'' (embed (rTS h)) qs init i"
term "config'' BIT qs init i"
lemma configCOMB: "i \<le> length qs \<Longrightarrow> config'' (COMB h) qs init i = do {
                    (b::bool) \<leftarrow> (bernoulli_pmf 0.8); 
                    (b1,b2) \<leftarrow>  (config'' BIT qs init i);
                    (t1,t2) \<leftarrow>  (config'' (embed (rTS h)) qs init i);
                    return_pmf (if b then  (b1, CBit b2) else (t1, CTs t2))
                    }" (is "?Prem \<Longrightarrow> ?LHS = ?RHS i")
proof (induct i)
  case 0 
  show ?case
  apply(simp add: BIT_init_def COMB_def rTS_def map_pmf_def bind_return_pmf bind_assoc_pmf )
  apply(rule bind_pmf_cong)
    apply(simp) 
    apply(simp only: set_pmf_bernoulli)
      apply(case_tac x)
        by(simp_all) 
next
  case (Suc n) 
  from Suc(2) show ?case apply(simp add: take_Suc_conv_app_nth)
    apply(subst config'_rand_append)
    apply(subst Suc(1))
      apply(simp)
      apply(simp add: bind_return_pmf bind_assoc_pmf split_def config'_rand_append)
        apply(rule bind_pmf_cong)
          apply(simp) 
          apply(simp only: set_pmf_bernoulli)
            apply(case_tac x)
               by(simp_all add: COMB_def COMB_step_def rTS_def map_pmf_def split_def bind_return_pmf bind_assoc_pmf)
qed



lemma BITfin: "x<length qs
   \<Longrightarrow> finite (set_pmf  (config'_rand BIT  (BIT_init init \<bind>  (\<lambda>is. return_pmf (init, is)))
                      (take x qs)))"
apply (induct x)
  apply(simp add: BIT_init_def bv_finite)
  by(simp add: take_Suc_conv_app_nth config'_rand_append BIT_step_def)
  
lemma TSfin: "x<length qs 
  \<Longrightarrow> finite (set_pmf (config'_rand (\<lambda>s. return_pmf h, \<lambda>s r. return_pmf (TS_step_d s r))
                         (return_pmf (init, h))
                         (take x qs)))" 
apply (induct x)
  apply(simp add: BIT_init_def)
  by(simp add: take_Suc_conv_app_nth config'_rand_append split_def) 


lemma T_COMB_split: "T\<^sub>p_on_rand (COMB h) init qs = 0.2 * T\<^sub>p_on_rand (embed (rTS h))  init qs + 0.8 * T\<^sub>p_on_rand BIT  init qs"
proof -
  have A: "0.2 * T_on_rand (embed (rTS h))  init qs + 0.8 * T_on_rand BIT  init qs
      = setsum (%i. 0.2 * T\<^sub>p_on_rand_n (embed (rTS h)) init qs i + 0.8 * T\<^sub>p_on_rand_n BIT  init qs i) {..<length qs}"
        unfolding T_on_rand_as_sum
          by(simp only: setsum_right_distrib setsum.distrib) 


  show ?thesis unfolding A unfolding T_on_rand_as_sum
    apply(rule setsum.cong)
      apply(simp)
      apply(subst configCOMB)
        apply(simp)  
        unfolding rTS_def COMB_def  
        apply(simp add: bind_assoc_pmf bind_return_pmf split_def ) 
        apply(subst E_bernoulli3)
          apply(simp) apply(simp) 
          using BITfin[of _ qs init] TSfin[of _ qs]
          apply(simp add: split_def set_pmf_bernoulli BIT_step_def COMB_step_def)
        unfolding COMB_step_def BIT_init_def map_pmf_def apply(simp add: split_def)
        apply(simp add: bind_assoc_pmf)
        by(simp add: bind_return_pmf split_def )  
qed  
      

definition "COMB_state h x y i = do {
                    (b::bool) \<leftarrow> (bernoulli_pmf 0.8);
                    (l,v)  \<leftarrow> i;
                    return_pmf (if b then (l, CBit v) else ([x,y], CTs h))
                  }"

definition "COMB_initial init h x y = do {
                    (b::bool) \<leftarrow> (bernoulli_pmf 0.8);
                    (l,v)  \<leftarrow> (type0 init x y);
                    return_pmf (if b then (l,CBit v) else ([x,y], CTs h))
                  }"



lemma config2COMB: "i \<le> length qs \<Longrightarrow> config2 (COMB h) qs (COMB_state h x y BI) i = do {
                    (b::bool) \<leftarrow> (bernoulli_pmf 0.8); 
                    (b1,b2) \<leftarrow>  (config2 BIT qs BI i);
                    (t1,t2) \<leftarrow>  config2 (embed (rTS h)) qs (return_pmf ([x, y], h)) i;
                    return_pmf (if b then  (b1, CBit b2) else (t1, CTs t2))
                    }" (is "?Prem \<Longrightarrow> ?LHS = ?RHS i")
proof (induct i)
  case 0 
  show ?case by(simp add: config2_def COMB_state_def bind_return_pmf) 
next
  case (Suc n) 
  from Suc(2) show ?case apply(simp add: config2_def take_Suc_conv_app_nth)
    apply(subst config'_rand_append)
    apply(subst Suc(1)[unfolded config2_def])
      apply(simp)
      apply(simp add: bind_return_pmf bind_assoc_pmf split_def config'_rand_append)
        apply(rule bind_pmf_cong)
          apply(simp) 
          apply(simp only: set_pmf_bernoulli)
            apply(case_tac xa)
               by(simp_all add: COMB_def COMB_step_def rTS_def map_pmf_def split_def bind_return_pmf bind_assoc_pmf)
qed


lemma configCOMB2asd: "config'_rand (COMB h) (COMB_state h x y i) qs  = do {
                    (b::bool) \<leftarrow> (bernoulli_pmf 0.8); 
                    (b1,b2) \<leftarrow>  (config'_rand BIT i qs);
                    (t1,t2) \<leftarrow>  (config'_rand (embed (rTS h)) (return_pmf ([x,y],h)) qs);
                    return_pmf (if b then  (b1, CBit b2) else (t1, CTs t2))
                    }" (is "?LHS = ?RHS i")
proof (induct qs rule: rev_induct)
  case Nil
  show ?case
  by(simp add: COMB_state_def BIT_init_def COMB_def rTS_def map_pmf_def bind_return_pmf bind_assoc_pmf )
next
  case (snoc r rs) 
  show ?case apply(simp add: take_Suc_conv_app_nth)
    apply(subst config'_rand_append)
    apply(subst snoc(1))
      apply(simp)
      apply(simp add: bind_return_pmf bind_assoc_pmf split_def config'_rand_append)
        apply(rule bind_pmf_cong)
          apply(simp) 
          apply(simp only: set_pmf_bernoulli)
            apply(case_tac xa)
               by(simp_all add: COMB_def COMB_step_def rTS_def map_pmf_def split_def bind_return_pmf bind_assoc_pmf)
qed

 
lemma T2_COMB_split: assumes "finite (set_pmf i)"
  shows "T\<^sub>p_on2 (COMB h) qs (COMB_state h x y i)
           = 0.2 * T\<^sub>p_on2 (embed (rTS h)) qs (return_pmf ([x,y],h))
            + 0.8 * T\<^sub>p_on2 BIT qs i"
proof -
  have A: "0.2 * T\<^sub>p_on2 (embed (rTS h)) qs (return_pmf ([x,y],h))
            + 0.8 * T\<^sub>p_on2 BIT qs i 
      = setsum (\<lambda>j. 0.2 * T_on_rand'_n (embed (rTS h)) (return_pmf ([x, y], h)) qs j
            + 0.8 * T_on_rand'_n BIT i qs j) {..<length qs}"
        unfolding  T\<^sub>p_on2_def T_on_n2_def
          by(simp only: setsum_right_distrib setsum.distrib) 

  { fix xa 
    assume "xa<length qs "
    then have "finite (set_pmf (config'_rand BIT i (take xa qs)))"
    apply(induct xa)
      using assms apply(simp)
      by(simp add: take_Suc_conv_app_nth config'_rand_append split_def BIT_step_def)
  } note BIT_fin2=this

  show ?thesis unfolding A unfolding T\<^sub>p_on2_def T_on_n2_def
    apply(rule setsum.cong)
      apply(simp)  
      apply(subst configCOMB2asd)
        apply(simp)  
        unfolding rTS_def COMB_def  
        apply(simp add: bind_assoc_pmf  bind_return_pmf split_def )         
        apply(subst E_bernoulli3)
          apply(simp) apply(simp) 
          using BIT_fin2 TSfin[of _ qs]
          apply(simp add: split_def set_pmf_bernoulli BIT_step_def COMB_step_def)
        unfolding COMB_step_def BIT_init_def map_pmf_def apply(simp add: split_def)
        apply(simp add: bind_assoc_pmf)
        by(simp add: bind_return_pmf split_def )   
qed  



definition "pre_inv_COMB init x y h = (h=[] \<or> (\<exists>hs. h = [x,x]@hs))"
definition "inv_COMB init qs x y h = (inv_BIT init qs x y \<and> inv_TS qs x y h)"

lemma TS_help: "T\<^sub>p_on_rand (embed (rTS h)) [x,y] qs
      = T\<^sub>p_on2 (embed (rTS h)) qs (return_pmf ([x,y],h))" 
    unfolding T\<^sub>p_on2_def T_on_n2_def T_on_rand_as_sum rTS_def by(simp add: bind_return_pmf)
 
lemma D: "qs \<in> Lxx x y \<Longrightarrow> x \<noteq> y \<Longrightarrow>
      pre_inv_COMB init x y h \<Longrightarrow> init \<in> {[x, y], [y, x]} \<Longrightarrow>
      T\<^sub>p_on2 (COMB h) qs (COMB_state h x y (type0 init x y)) \<le> 1.6 * T\<^sub>p [x, y] qs (OPT2 qs [x, y])
       \<and> inv_COMB init qs x y h"
proof (rule LxxI[where P="(\<lambda>x y qs.  T\<^sub>p_on2 (COMB h) qs (COMB_state h x y (type0 init x y)) \<le> 1.6 * T\<^sub>p [x, y] qs (OPT2 qs [x, y]) \<and>
                                   inv_COMB init qs x y h)"], goal_cases)
  case 1
  from 1(3)[unfolded pre_inv_COMB_def inv_TS_def] obtain x' y' where "x'=x" and "y'=y" 
      and h: "h=[] \<or> (\<exists>hs. h = [x, x] @ hs)" unfolding s_TS_def by(auto)
  from ts_d[OF 1(1,2) h 1(5)]
  have "real (T_TS [x, y] h qs) = 0"
      and TS_inv: "inv_TS qs x y h"  by auto
  then have "T\<^sub>p_on_rand (embed (rTS h)) [x,y] qs = 0" using T_TS_T_on T_on_embed by metis
  then have TS: "T\<^sub>p_on2 (embed (rTS h)) qs (return_pmf ([x,y],h)) = 0" using TS_help by metis
  have BIT: "T\<^sub>p_on2 BIT qs (type0 init x y)  = 0" apply(rule BIT_d) using 1 by auto
  have BIT_inv: "inv_BIT init qs x y" unfolding inv_BIT_def apply(rule BIT_d_config) using 1 by auto

  have "T\<^sub>p_on2 (COMB h) qs (COMB_state h x y (type0 init x y)) 
      = 0.2 * T\<^sub>p_on2 (embed (rTS h)) qs (return_pmf ([x,y],h))
            + 0.8 * T\<^sub>p_on2 BIT qs (type0 init x y)"
    apply(rule T2_COMB_split) 
      by(simp add: type0_def)
  also have "\<dots> = 0" using TS BIT by simp
  also have "\<dots> \<le> 1.6 * T\<^sub>p [x, y] qs (OPT2 qs [x, y])" by simp
  finally show ?case unfolding inv_COMB_def using BIT_inv TS_inv by auto
next
  case 2  
  obtain u v where uu: "u \<in> lang (Plus (Atom x) One)"
    and vv: "v \<in> lang (seq[Times (Atom y) (Atom x), Star (Times (Atom y) (Atom x)), Atom y, Atom y])"
    and qsuv: "qs = u @ v" 
    using 2
    by (auto simp: conc_def) 

  have lenv: "length v > 1 \<and> last v = y \<and> v\<noteq>[]"
  proof -
    from vv have "v \<in> ({[y]} @@ {[x]}) @@ star({[y]} @@ {[x]}) @@ {[y]} @@ {[y]}" by(simp add: conc_assoc)
    then obtain p q r where pqr: "v=p@q@r" and "p\<in>({[y]} @@ {[x]})"
              and q: "q \<in> star ({[y]} @@ {[x]})" and "r \<in>{[y]} @@ {[y]}" by (metis concE)
    then have rr: "p = [y,x]" "r=[y,y]" by auto
    with pqr have a: "length v = 4+length q" by auto

    have "last v = last r" using pqr rr by auto
    then have c: "last v = y" using rr by auto
    with a show ?thesis by auto
  qed


  (* TS *)  
  from 2(3)[unfolded pre_inv_COMB_def inv_TS_def] obtain x' y' where "x'=x" and "y'=y" 
      and h: "h=[] \<or> (\<exists>hs. h = [x, x] @ hs)" unfolding s_TS_def by(auto)
  from TS_xr[OF 2(2) uu h]
  have  TS_1: "T_TS [x, y] h (u@v) = T_TS [x,y] (rev u @ h) v"
    and TS_2: "(\<exists>hs. (rev u @ h) = [x, x] @ hs) \<or> (rev u @ h) = [x] \<or> (rev u @ h)=[]" by auto
  from ts_b[OF 2(2) vv TS_2]
  have  TS_3: "T_TS [x, y] (rev u @ h) v = (length v - 2)"
         and  inv1: "s_TS [x,y] (rev u @ h) v (length v) = [y,x]"
         and  inv2: "(\<exists>hs. (rev v @ (rev u @ h)) = [y,y]@hs)" by auto
  have "T\<^sub>p_on_rand (embed (rTS h))  [x,y] qs = (length v - 2)"
    unfolding  qsuv using T_on_embed T_TS_T_on TS_1 TS_3 by metis
  then have TS: "T\<^sub>p_on2 (embed (rTS h)) qs (return_pmf ([x,y],h)) = (length v - 2)" using TS_help by metis

  have splitdet1: "TSdet [x,y] h (u @ v) (length (u @ v))
      = TSdet (fst (TSdet [x,y] h u (length u))) (rev u @ h) v (length v)" 
        using splitdet by auto 

  have first: "fst (TSdet [x,y] h u (length u)) = [x,y]"
    apply(cases "u=[]")
      apply(simp )
      using uu by(simp add: rTS_def Step_def TS_step_d_def step_def)
  
  have 1: "s_TS [x, y] h qs (length qs) = [y, x]"
    unfolding s_TS_def qsuv apply(simp only: splitdet1)
    by(simp only: first inv1[unfolded s_TS_def]) 
  
  have TS_inv: "inv_TS qs x y h" unfolding inv_TS_def
     apply(rule exI[where x="y"])
     apply(rule exI[where x="x"]) 
      using 1 inv2 qsuv by(auto) 

  (* BIT *)
  from BIT_b[OF 2(2,4) vv ] have BITv: "T\<^sub>p_on2 BIT v (type0 init x y) = 3/4 *  ( length v) - 0.5" 
            and b_c: "config2 BIT v (type0 init x y) (length v) = type0 init y x" by auto
  from BIT_x[OF 2(2,4) uu] have BITu: "T\<^sub>p_on2 BIT (u @ v) (type0 init x y) = T\<^sub>p_on2 BIT v (type0 init x y)"
            and x_c: "config2 BIT u (type0 init x y) (length u) = type0 init x y" by auto
  from BITu BITv have BIT: "T\<^sub>p_on2 BIT qs (type0 init x y) = 0.75 * length v - 0.5"
        using qsuv  2(4) by auto  


  have "config2 BIT (u @ v) (type0 init x y) (length (u @ v)) =
         config2 BIT v (config2 BIT u (type0 init x y) (length u)) (length v)"
          by (simp add: config2_append_ge)
  also have "\<dots> = type0 init y x" by (auto simp add: x_c b_c)
  finally have config: "config2 BIT qs (type0 init x y) (length qs) = type0 init y x" using qsuv by auto
  from lenv have "v \<noteq> []"  "last v = y" by auto
  then have 1:  "last qs = y" using last_appendR qsuv by simp 
  then have f2: "other (last qs) x y = x" unfolding other_def by simp  
  
  from 1 f2 config have BIT_inv: "inv_BIT init qs x y" unfolding inv_BIT_def by auto

  (* OPT *)
  from uu have u2: "u = [] \<or> u = [x]"  by auto
  have OPT: "T\<^sub>p [x,y] qs (OPT2 qs [x,y]) = (length v div 2)" using OPT2_B[OF 2(2) qsuv u2 vv] by simp


  (* calculation *)
  have "T\<^sub>p_on2 (COMB h) qs (COMB_state h x y (type0 init x y)) 
      = 0.2 * T\<^sub>p_on2 (embed (rTS h)) qs (return_pmf ([x,y],h))
            + 0.8 * T\<^sub>p_on2 BIT qs (type0 init x y)"
    apply(rule T2_COMB_split)
      by(simp add: type0_def)
  also have "\<dots> = 0.2 * (length v - 2) + 0.8 * (0.75 * length v - 0.5)" using TS BIT by simp
  also have "\<dots> \<le> 1.6 * (length v div 2)"
  proof -
    have A: "length v \<ge>2" using lenv by auto
    have "2 * (length v - 2) + 8 * (0.75 * length v - 0.5)
          = 8 * length v - 8" using A by(auto simp: ring_distribs)
    also have "\<dots> \<le> 8*( 2*(length v div 2) +1 ) - 8" by auto
    also have "\<dots> = 16 * (length v div 2)" by auto
    finally have 1: "2 * (length v - 2) + 8 * (0.75 * length v - 0.5) \<le> 16 * (length v div 2)" .

    have " 0.2 * (length v - 2) + 0.8 * (0.75 * length v - 0.5)
        = 1/10 * (2 * (length v - 2) + 8 * (0.75 * length v - 0.5))" by auto
    also have "\<dots> \<le> 1/10 * (16 * (length v div 2))" using 1 by auto
    also have "\<dots> = 1.6 * (length v div 2)" by auto
    finally show ?thesis .
  qed
  also have "\<dots> = 1.6 * T\<^sub>p [x, y] qs (OPT2 qs [x, y])" using OPT by simp
  finally show ?case unfolding inv_COMB_def using BIT_inv TS_inv by auto
next
  case 3
  obtain u v where uu: "u \<in> lang (Plus (Atom x) One)"
    and vv: "v \<in> lang (seq[Times (Atom y) (Atom x), Star (Times (Atom y) (Atom x)), Atom x])"
    and qsuv: "qs = u @ v" 
    using 3
    by (auto simp: conc_def) 

  have lenv: "length v > 1 \<and> last v = x \<and> v\<noteq>[]"
  proof -
    from vv have "v \<in> ({[y]} @@ {[x]}) @@ star({[y]} @@ {[x]}) @@ {[x]}" by(simp add: conc_assoc)
    then obtain p q r where pqr: "v=p@q@r" and "p\<in>({[y]} @@ {[x]})"
              and q: "q \<in> star ({[y]} @@ {[x]})" and "r \<in>{[x]}" by (metis concE)
    then have rr: "p = [y,x]" "r=[x]" by auto
    with pqr have a: "length v = 3+length q" by auto

    have "last v = last r" using pqr rr by auto
    then have c: "last v = x" using rr by auto
    with a show ?thesis by auto
  qed



  (* TS *)  
  from 3(3)[unfolded pre_inv_COMB_def inv_TS_def] obtain x' y' where "x'=x" and "y'=y" 
      and h: "h=[] \<or> (\<exists>hs. h = [x, x] @ hs)" unfolding s_TS_def by(auto)
  from TS_xr[OF 3(2) uu h]
  have  TS_1: "T_TS [x, y] h (u@v) = T_TS [x,y] (rev u @ h) v"
    and TS_2: "(\<exists>hs. (rev u @ h) = [x, x] @ hs) \<or> (rev u @ h) = [x] \<or> (rev u @ h)=[]" by auto
  from ts_c[OF 3(2) vv TS_2]
  have  TS_3: "T_TS [x, y] (rev u @ h) v = (length v - 2)"
         and  inv1: "s_TS [x,y] (rev u @ h) v (length v) = [x,y]"
         and  inv2: "(\<exists>hs. (rev v @ (rev u @ h)) = [x,x]@hs)" by auto
  have "T\<^sub>p_on_rand (embed (rTS h))  [x,y] qs = (length v - 2)"
    unfolding  qsuv using T_TS_T_on TS_1 TS_3 T_on_embed by metis
  then have TS: "T\<^sub>p_on2 (embed (rTS h)) qs (return_pmf ([x,y],h)) = (length v - 2)" using TS_help by metis


  have splitdet1: "TSdet [x,y] h (u @ v) (length (u @ v))
      = TSdet (fst (TSdet [x,y] h u (length u))) (rev u @ h) v (length v)" 
        using splitdet by auto 

  have first: "fst (TSdet [x,y] h u (length u)) = [x,y]"
    apply(cases "u=[]")
      apply(simp add:)
      using uu by(simp add: rTS_def Step_def  TS_step_d_def step_def)
  
  have 1: "s_TS [x, y] h qs (length qs) = [x, y]"
    unfolding s_TS_def qsuv apply(simp only: splitdet1)
    by(simp only: first inv1[unfolded s_TS_def]) 
  
  have TS_inv: "inv_TS qs x y h" unfolding inv_TS_def
     apply(rule exI[where x="x"])
     apply(rule exI[where x="y"]) 
      using 1 inv2 qsuv by(auto) 

  (* BIT *) 
  from BIT_c[OF 3(2,4) vv] have BITv: "T\<^sub>p_on2 BIT v (type0 init x y) = 0.75 * length v - 0.5" 
            and c_c: "config2 BIT v (type0 init x y) (length v) = type0 init  x y" by auto
  from BIT_x[OF 3(2,4) uu] have BITu: "T\<^sub>p_on2 BIT (u @ v) (type0 init x y) = T\<^sub>p_on2 BIT v (type0 init x y)"
            and x_c: "config2 BIT u (type0 init x y) (length u) = type0 init x y" by auto
  from BITu BITv have BIT: "T\<^sub>p_on2 BIT qs (type0 init x y) = 0.75 * length v - 0.5"
        using qsuv by auto
  


  have "config2 BIT (u @ v) (type0 init x y) (length (u @ v)) =
         config2 BIT v (config2 BIT u (type0 init x y) (length u)) (length v)"
          by (simp add: config2_append_ge)
  also have "\<dots> = type0 init x y" by (auto simp add: x_c c_c)
  finally have config: "config2 BIT qs (type0 init x y) (length qs) = type0 init x y" using qsuv by auto
  from lenv have "v \<noteq> []"  "last v = x" by auto
  then have 1:  "last qs = x" using last_appendR qsuv by simp 
  then have 2: "other (last qs) x y = y" unfolding other_def by simp  
  
  from 1 2 config have BIT_inv: "inv_BIT init qs x y" unfolding inv_BIT_def by auto


  (* OPT *)
  from uu have u2: "u = [] \<or> u = [x]"  by auto
  have OPT: "T\<^sub>p [x,y] qs (OPT2 qs [x,y]) = (length v div 2)" apply(rule OPT2_C) using 3(2) qsuv u2 vv by(simp_all add: conc_assoc)


  (* calculation *)  
  have "T\<^sub>p_on2 (COMB h) qs (COMB_state h x y (type0 init x y)) 
      = 0.2 * T\<^sub>p_on2 (embed (rTS h)) qs (return_pmf ([x,y],h))
            + 0.8 * T\<^sub>p_on2 BIT qs (type0 init x y)"
    apply(rule T2_COMB_split)
      by(simp add: type0_def)
  also have "\<dots> = 0.2 * (length v - 2) + 0.8 * (0.75 * length v - 0.5)" using TS BIT by simp
  also have "\<dots> \<le> 1.6 * (length v div 2)"
  proof -
    have A: "length v \<ge>2" using lenv by auto
    have "2 * (length v - 2) + 8 * (0.75 * length v - 0.5)
          = 8 * length v - 8" using A by(auto simp: ring_distribs)
    also have "\<dots> \<le> 8*( 2*(length v div 2) +1 ) - 8" by auto
    also have "\<dots> = 16 * (length v div 2)" by auto
    finally have 1: "2 * (length v - 2) + 8 * (0.75 * length v - 0.5) \<le> 16 * (length v div 2)" .

    have " 0.2 * (length v - 2) + 0.8 * (0.75 * length v - 0.5)
        = 1/10 * (2 * (length v - 2) + 8 * (0.75 * length v - 0.5))" by auto
    also have "\<dots> \<le> 1/10 * (16 * (length v div 2))" using 1 by auto
    also have "\<dots> = 1.6 * (length v div 2)" by auto
    finally show ?thesis .
  qed
  also have "\<dots> = 1.6 * T\<^sub>p [x, y] qs (OPT2 qs [x, y])" using OPT by simp
  finally show ?case unfolding inv_COMB_def using BIT_inv TS_inv by auto
next
  case 4
  then have lqs: "last qs = y" by fastforce
  from 4(3)[unfolded pre_inv_COMB_def inv_TS_def] obtain x' y' where "x'=x" and "y'=y" 
      and h: "h=[] \<or> (\<exists>hs. h = [x, x] @ hs)" unfolding s_TS_def by(auto)
  from ts_a[OF 4(2,5) h]
  have "real (T_TS [x, y] h qs) = 2" 
      and TS_inv: "inv_TS qs x y h" by auto
  then have "T\<^sub>p_on_rand (embed (rTS h)) [x,y] qs = 2"
      using T_TS_T_on T_on_embed by metis
  then have TS: "T\<^sub>p_on2 (embed (rTS h)) qs (return_pmf ([x,y],h)) = 2" using TS_help by metis

  have BIT: "T\<^sub>p_on2 BIT qs (type0 init x y) = 1.5" apply(rule BIT_a) using 4 by auto
  have BIT_inv: "inv_BIT init qs x y" unfolding inv_BIT_def other_def
    using lqs BIT_a_config[OF 4(1,2,4,5)] by auto

  (* OPT *)
  have OPT: "T\<^sub>p [x,y] qs (OPT2 qs [x,y]) = 1" using OPT2_A[OF 4(2,5)] by auto

  have "T\<^sub>p_on2 (COMB h) qs (COMB_state h x y (type0 init x y)) 
      = 0.2 * T\<^sub>p_on2 (embed (rTS h)) qs (return_pmf ([x,y],h))
            + 0.8 * T\<^sub>p_on2 BIT qs (type0 init x y)"
    apply(rule T2_COMB_split)
      by(simp add: type0_def)
  also have "\<dots> = 1.6" using TS BIT by simp
  also have "\<dots> \<le> 1.6 * T\<^sub>p [x, y] qs (OPT2 qs [x, y])" using OPT by simp
  finally show ?case unfolding inv_COMB_def using BIT_inv TS_inv by auto
qed simp
    

lemma config2_COMB: "i<length qs \<Longrightarrow> config2 (COMB h1) qs initdistr i = config2 (COMB h2) qs initdistr i"
apply(induct i) by(simp_all add: COMB_def config2_def take_Suc_conv_app_nth config'_rand_append)

lemma h_indifferent: "T\<^sub>p_on2 (COMB h1) qs initdistr = T\<^sub>p_on2 (COMB h2) qs initdistr"
unfolding T\<^sub>p_on2_def
  apply(rule setsum.cong)
    apply(simp)
     unfolding T_on_n2_def
     apply(simp)
     apply(subst config2_COMB[of _ _ _ _ h2, unfolded config2_def]) by (simp_all add: COMB_def) 
            
theorem COMB_OPT2: "(x::nat) \<noteq> y
     \<Longrightarrow> pre_inv_COMB init x y h
     \<Longrightarrow> init\<in>{[x,y],[y,x]}
     \<Longrightarrow> set \<sigma> \<subseteq> {x,y}
     \<Longrightarrow> T\<^sub>p_on2 (COMB h) \<sigma> (COMB_state h x y (type0 init x y)) \<le> 1.6 * T\<^sub>p [x,y] \<sigma> (OPT2 \<sigma> [x,y]) + 2"
 proof (induction "length \<sigma>" arbitrary: \<sigma> x y h rule: less_induct)
  case (less \<sigma>)
  let ?initstate = "(COMB_state h x y (type0 init x y))" 

  show ?case
  proof (cases "\<exists>xs ys. \<sigma>=xs@ys \<and> xs \<in> Lxx x y")
    case True 

    then obtain xs ys where qs: "\<sigma>=xs@ys" and xsLxx: "xs \<in> Lxx x y" by auto

    with Lxx1 have len: "length ys < length \<sigma>" by fastforce
    from qs(1) less(5) have ysxy: "set ys \<subseteq> {x,y}" by auto


    have xsset: "set xs \<subseteq> {x, y}" using less(5) qs by auto
    from xsLxx Lxx1 have lxsgt1: "length xs \<ge> 2" by auto
    then have xs_not_Nil: "xs \<noteq> []" by auto

    from D[OF xsLxx less(2-4)]
      have D1: "T\<^sub>p_on2 (COMB h) xs (COMB_state h x y (type0 init x y)) \<le> 1.6 * T\<^sub>p [x, y] xs (OPT2 xs [x, y])" 
         and invCOMB: "inv_COMB init xs x y h" by auto

    from invCOMB[unfolded inv_COMB_def inv_TS_def inv_BIT_def]
      have invBIT: "config2 BIT xs (type0 init x y) (length xs) = type0 init (last xs) (other (last xs) x y)" 
      and invTS: "(\<exists>x' y'. s_TS [x, y] h xs (length xs) = [x', y'] \<and> (\<exists>hs. rev xs @ h = [x', x'] @ hs))" by auto
 
     have "s_TS [x, y] h xs (length xs) = [last xs, other (last xs) x y]"
        and invTS_2: "(\<exists>hs. rev xs @ h = [last xs, last xs] @ hs)"  
        and invTS_config2: "config2 (embed (rTS h)) xs (return_pmf ([x, y], h)) (length xs)
            = return_pmf ([last xs, other (last xs) x y], rev xs@h)"
      proof (goal_cases)
        from invTS obtain x' y' hs where f1: "s_TS [x, y] h xs (length xs) = [x', y']"
                and h: "rev xs @ h = [x', x'] @ hs" by auto
        have "hd (rev xs @ h) = x'" using h by auto
        with xs_not_Nil have "hd (rev xs) = x'" by(auto)
        with xs_not_Nil hd_rev have xlast: "x' = last xs" by metis
        from s_TS_xy[OF less(2) xsset, of "length xs" h] less(2) f1 have
            xyxy: "[x', y'] \<in> {[x,y], [y,x]}" by force
        have "x'\<noteq>y'" and "(x'=x \<and> y'=y) \<or> (x'=y \<and> y'=x)"
            using xyxy less(2) by auto
        then have yother: "y' = other x' x y" unfolding other_def by auto
        case 1
        show fstTS: ?case using f1 xlast yother by auto
        case 2
        show ?case using h xlast by auto
        case 3
        have sndTS: "snd (TSdet [x,y] h xs (length xs)) = (rev xs)@h"
          apply(subst sndTSdet) by(auto)
 
        have "config2 (embed (rTS h)) xs (return_pmf ([x, y], h)) (length xs) 
              = config'' (embed (rTS h)) xs [x,y] (length xs)"
          unfolding rTS_def config2_def by(simp add: bind_return_pmf)
        also have "\<dots> =  (return_pmf ( TSdet [x,y] h xs (length xs)))"
             apply(subst config_embed) by simp
        also have "\<dots> = return_pmf ([last xs, other (last xs) x y], rev xs@h)"
          using sndTS fstTS[unfolded s_TS_def]  apply(cases " TSdet [x,y] h xs (length xs)")
            by(simp) 
        finally  show ?case .
    qed

    from xsLxx Lxx_ends_in_two_equal obtain pref e where "xs = pref @ [e,e]" by metis
    then have endswithsame: "xs = pref @ [last xs, last xs]" by auto 

    let ?c' = "[last xs, other (last xs) x y]" 

    have setys: "set ys \<subseteq> {x,y}" using qs less by auto 
    have setxs: "set xs \<subseteq> {x,y}" using qs less by auto 
    have lxs: "last xs \<in> set xs" using xs_not_Nil by auto
    from lxs setxs have lxsxy: "last xs \<in> {x,y}" by auto 
     from lxs setxs have otherxy: "other (last xs) x y \<in> {x,y}" by (simp add: other_def)
    from less(2) have other_diff: "last xs \<noteq> other (last xs) x y" by(simp add: other_def)
 
    have nextstate: "{[last xs, other (last xs) x y], [other (last xs) x y, last xs]}
            = { [x,y],[y,x]}" using lxsxy otherxy other_diff by fastforce
    have setys': "set ys \<subseteq> {last xs, other (last xs) x y}"
            using setys lxsxy otherxy other_diff by fastforce

    let ?nextstate = "(COMB_state (rev xs @ h) (last xs) (other (last xs) x y) (type0 init (last xs) (other (last xs) x y)))"

    have yeaah: "config2 (COMB h) xs ?initstate (length xs)  = ?nextstate"
      apply(subst config2COMB)
        apply(simp)
        apply(subst invBIT) 
        apply(subst invTS_config2)
        unfolding COMB_state_def by(simp add: bind_return_pmf)  

    have "T\<^sub>p_on2 (COMB h)  ys (config2 (COMB h)  xs ?initstate (length xs))
        = T\<^sub>p_on2 (COMB h)  ys ?nextstate"
          by(simp only: yeaah)  
    also have "\<dots> = T\<^sub>p_on2 (COMB (rev xs @ h))  ys ?nextstate"
      using h_indifferent by auto
    also from len have "\<dots> \<le> 1.6 * T\<^sub>p ?c' ys (OPT2 ys ?c') + 2"       
            apply(rule less(1))
              using less(2) apply(simp add: other_def)
              unfolding pre_inv_COMB_def using invTS_2 apply(simp) 
              using less(4) nextstate apply(simp) 
              by(fact setys')
     finally have c: "T\<^sub>p_on2 (COMB h)  ys (config2 (COMB h)  xs ?initstate (length xs))
                  \<le> 1.6 * T\<^sub>p ?c' ys (OPT2 ys ?c') + 2" .


    have well: "T\<^sub>p [x, y] xs (OPT2 xs [x, y]) + T\<^sub>p ?c' ys (OPT2 ys ?c')
        = T\<^sub>p [x, y] (xs @ ys) (OPT2 (xs @ ys) [x, y])"
          apply(rule OPTauseinander[where pref=pref])
            apply(fact)+
            using lxsxy other_diff otherxy apply(fastforce)
            apply(simp)
            using endswithsame by simp  

    have E0: " T\<^sub>p_on2 (COMB h) \<sigma> ?initstate
          =  T\<^sub>p_on2 (COMB h) (xs@ys) ?initstate" using qs by auto
     also have E1: "\<dots> = T\<^sub>p_on2 (COMB h) xs ?initstate
              + T\<^sub>p_on2 (COMB h)  ys (config2 (COMB h)  xs ?initstate (length xs))"
      unfolding COMB_def  by (rule splitquerylist2)
    also have E2: "\<dots> \<le> T\<^sub>p_on2 (COMB h) xs ?initstate + 1.6 * T\<^sub>p ?c' ys (OPT2 ys ?c') + 2"
        using c by simp
    also have E3: "\<dots> \<le> 1.6 * T\<^sub>p [x, y] xs (OPT2 xs [x, y]) + 1.6 * T\<^sub>p ?c' ys (OPT2 ys ?c') + 2"
        using D1 by simp        
    also have "\<dots> \<le> 1.6 * (T\<^sub>p [x,y] xs (OPT2 xs [x,y]) + T\<^sub>p ?c' ys (OPT2 ys ?c')) + 2"
        by(auto)
    also have  "\<dots> = 1.6 * (T\<^sub>p [x,y] (xs@ys) (OPT2 (xs@ys) [x,y])) + 2"
      using well by auto 
    also have E4: "\<dots> = 1.6 * (T\<^sub>p [x,y] \<sigma> (OPT2 \<sigma> [x,y])) + 2"
        using qs by auto
    finally show ?thesis .
 

  next
    case False
    note f1=this
    from Lxx_othercase[OF less(5) this, unfolded hideit_def] have
        nodouble: "\<sigma> = [] \<or> \<sigma> \<in> lang (nodouble x y)" by  auto
    show ?thesis
    proof (cases "\<sigma> = []")
      case True
      then show ?thesis unfolding T\<^sub>p_on2_def  by(simp)
    next
      case False
      (* with padding *)
      from False nodouble have qsnodouble: "\<sigma> \<in> lang (nodouble x y)" by auto
      let ?padded = "pad \<sigma> x y"
      from False pad_adds2[of \<sigma> x y] less(5) obtain addum where ui: "pad \<sigma> x y = \<sigma> @ [last \<sigma>]" by auto
      from nodouble_padded[OF False qsnodouble] have pLxx: "?padded \<in> Lxx x y" .

      have E0: "T\<^sub>p_on2 (COMB h) \<sigma> ?initstate \<le> T\<^sub>p_on2 (COMB h) ?padded ?initstate"
      proof -
        have "T\<^sub>p_on2 (COMB h) \<sigma> ?initstate = setsum (T_on_n2 (COMB h) \<sigma> ?initstate) {..<length \<sigma>}"
          unfolding T\<^sub>p_on2_def by simp
        also have "\<dots>
             = setsum (T_on_n2 (COMB h) (\<sigma> @ [last \<sigma>]) ?initstate) {..<length \<sigma>}"
          proof(rule setsum.cong, goal_cases)
            case (2 t)
            then have "t < length \<sigma>" by auto 
            then show ?case unfolding T_on_n2_def by(simp add: nth_append)
          qed simp
        also have "... \<le> T\<^sub>p_on2 (COMB h) ?padded ?initstate"
          unfolding ui T\<^sub>p_on2_def apply(simp)
          unfolding COMB_def T_on_n2_def by(simp only: T_on_rand'_nn) 
        finally show ?thesis by auto
      qed  

      also from pLxx have E1: "\<dots> \<le> 1.6 * T\<^sub>p [x,y] ?padded (OPT2 ?padded [x,y])"
        using D[OF pLxx less(2-4) ] by simp
      also have E2: "\<dots> \<le> 1.6 * T\<^sub>p [x,y] \<sigma> (OPT2 \<sigma> [x,y]) + 2"
      proof -
        from False less(2) obtain \<sigma>' x' y' where qs': "\<sigma> = \<sigma>' @ [x']" and x': "x' = last \<sigma>" "y'\<noteq>x'" "y' \<in>{x,y}" 
            by (metis append_butlast_last_id insert_iff)
        have tla: "last \<sigma> \<in> {x,y}" using less(5) False last_in_set by blast
        with x' have grgr: "{x,y} = {x',y'}" by auto
        then have "(x = x' \<and> y = y') \<or> (x = y' \<and> y = x')" using less(2) by auto
        then have tts: "[x, y] \<in> {[x', y'], [y', x']}" by blast
        
        from qs' ui have pd: "?padded = \<sigma>' @ [x', x']" by auto 

        have "T\<^sub>p [x,y] (?padded) (OPT2 (?padded) [x,y])
              = T\<^sub>p [x,y] (\<sigma>' @ [x', x']) (OPT2 (\<sigma>' @ [x', x']) [x,y])"
                unfolding pd by simp
        also have gr: "\<dots>
            \<le> T\<^sub>p [x,y] (\<sigma>' @ [x']) (OPT2 (\<sigma>' @ [x']) [x,y]) + 1"
              apply(rule OPT2_padded[where x="x'" and y="y'"])
                apply(fact)
                using grgr qs' less(5) by auto
        also have "\<dots> \<le> T\<^sub>p [x,y] (\<sigma>) (OPT2 (\<sigma>) [x,y]) + 1" 
              unfolding qs' by simp
        finally show ?thesis by auto
      qed
      finally show ?thesis .  
    qed
  qed 
qed  


theorem COMB_on2: assumes
 "set \<sigma> \<subseteq> {x,y}" and  "(x::nat) \<noteq> y"
  shows
      "T\<^sub>p_on_rand (COMB []) [x,y] \<sigma>  \<le> 1.6 * T\<^sub>p_opt [x, y] \<sigma> + 2"
proof -
  have pre: "pre_inv_COMB [x,y] x y []" unfolding pre_inv_COMB_def by simp

  have "T\<^sub>p_on_rand (COMB []) [x,y] \<sigma> = 
         T\<^sub>p_on2 (COMB []) \<sigma> (COMB_state [] x y (type0 [x,y] x y))"
         unfolding T\<^sub>p_on2_def T_on_rand_as_sum T_on_n2_def COMB_state_def COMB_def
         apply(rule setsum.cong)
          apply(simp)
          apply(simp add: type0_def bind_return_pmf bind_assoc_pmf)
          apply(rule arg_cong[where f=E])
          apply(rule bind_pmf_cong)
            apply(simp_all)
            apply(rule arg_cong2[where f="config'_rand (COMB_init [], COMB_step)"])
              apply(rule bind_pmf_cong)
                apply(simp add: set_pmf_bernoulli)
                  apply(case_tac xaa)
                    apply(simp) using bind_commute_pmf apply fast
                    apply(simp)               
              apply(simp)
         done
  also have "\<dots> \<le> 1.6 * T\<^sub>p [x,y] \<sigma> (OPT2 \<sigma> [x,y]) + 2"
    apply(rule COMB_OPT2)
      using assms pre by (simp_all)
  also have "\<dots> = 1.6 * T\<^sub>p_opt [x, y] \<sigma> + 2"
    using OPT2_is_opt[OF assms] by(simp)
  finally show ?thesis .
qed





subsubsection "COMB pairwise"


lemma config_rand_COMB: "config_rand (COMB h) init qs = do {
                    (b::bool) \<leftarrow> (bernoulli_pmf 0.8); 
                    (b1,b2) \<leftarrow>  (config_rand BIT init qs);
                    (t1,t2) \<leftarrow>  (config_rand (embed (rTS h)) init qs);
                    return_pmf (if b then  (b1, CBit b2) else (t1, CTs t2))
                    }" (is "?LHS = ?RHS")
proof (induct qs rule: rev_induct)
  case Nil
  show ?case
  apply(simp add: BIT_init_def COMB_def rTS_def map_pmf_def bind_return_pmf bind_assoc_pmf )
  apply(rule bind_pmf_cong)
    apply(simp) 
    apply(simp only: set_pmf_bernoulli)
      apply(case_tac x)
        by(simp_all) 
next
  case (snoc q qs) 
  show ?case apply(simp add: take_Suc_conv_app_nth)
    apply(subst config'_rand_append)
    apply(subst snoc)
      apply(simp)
      apply(simp add: bind_return_pmf bind_assoc_pmf split_def config'_rand_append)
        apply(rule bind_pmf_cong)
          apply(simp) 
          apply(simp only: set_pmf_bernoulli)
            apply(case_tac x)
               by(simp_all add: COMB_def COMB_step_def rTS_def map_pmf_def split_def bind_return_pmf bind_assoc_pmf)
qed

lemma COMB_pairwise: "pairwise (COMB [])"
proof(rule pairwise_property_lemma, goal_cases) 
  case (1 init qs x y)
  then have qsininit: "set qs \<subseteq> set init" by simp
  
  show "Pbefore_in x y (COMB []) qs init 
        = Pbefore_in x y (COMB []) (Lxy qs {x, y}) (Lxy init {x, y})"
        unfolding Pbefore_in_def
        apply(subst config_rand_COMB)  
        apply(subst config_rand_COMB)  
        apply(simp only: map_pmf_def  bind_assoc_pmf)
        apply(rule bind_pmf_cong)
          apply(simp)
          apply(simp only: set_pmf_bernoulli)
          apply(case_tac xa)
            apply(simp add: split_def) 
              using BIT_pairwise'[OF qsininit 1(3,4,1), unfolded Pbefore_in_def map_pmf_def]
              apply(simp add: bind_return_pmf bind_assoc_pmf)
            apply(simp add: split_def) 
              using TS_pairwise'[OF 1(2,3,4,1), unfolded Pbefore_in_def map_pmf_def]
              by(simp add: bind_return_pmf bind_assoc_pmf)
next
  case (2 xa r)
  show ?case
    apply(simp add: COMB_def COMB_step_def split_def)
    apply(case_tac "snd xa")
      by(simp_all add: BIT_step_def TS_step_d_def)
qed 
          

subsubsection "COMB 1.6-competitive"



lemma finite_config_TS: "finite (set_pmf (config'' (embed (rTS h)) qs init n))" (is "finite ?D")
  apply(subst config_embed)
    by(simp)

lemma COMB_has_finite_config_set: assumes [simp]: "distinct init"
      and "set qs \<subseteq> set init"
      and "x<length qs"
      shows "finite (set_pmf (config'' (COMB h) qs init x))"
proof -
  show ?thesis 
      apply(subst configCOMB)
        using assms(3) apply(simp)
        apply(subst set_bind_pmf)
          apply(simp only: set_pmf_bernoulli split_def)
          apply(rule finite_UN_I)
            apply(simp)
            apply(case_tac M)
              apply(simp)
              apply(rule finite_UN_I)
                using finite_config_BIT[OF assms(1)] apply auto[1]
                apply(simp)
              apply(simp)
              apply(rule finite_UN_I) 
                using finite_config_TS  apply auto[1]
                by simp
qed

lemma COMB_no_paid: " \<forall>((free, paid), t)\<in>set_pmf (snd (COMB []) (s, is) q). paid = []"
apply(simp add:  COMB_def COMB_step_def split_def BIT_step_def TS_step_d_def)
apply(case_tac "is")
  by(simp_all add: BIT_step_def TS_step_d_def)
  


theorem COMB_competitive: "\<forall>s0\<in>{x::nat list. distinct x \<and> x\<noteq>[]}.
   \<exists>b\<ge>0. \<forall>qs\<in>{x. set x \<subseteq> set s0}.
             T\<^sub>p_on_rand (COMB []) s0 qs \<le> ((8::nat)/(5::nat)) *  T\<^sub>p_opt s0 qs + b" 
proof(rule factoringlemma_withconstant, goal_cases)
  case 5
  show ?case 
    proof (safe, goal_cases)
      case (1 init)
      note out=this
      show ?case
        apply(rule exI[where x=2])
          apply(simp)
          proof (safe, goal_cases)
            case (1 qs a b)
            then have a: "a\<noteq>b" by simp
            have twist: "{a,b}={b, a}" by auto
            have b1: "set (Lxy qs {a, b}) \<subseteq> {a, b}" unfolding Lxy_def by auto
            with this[unfolded twist] have b2: "set (Lxy qs {b, a}) \<subseteq> {b, a}" by(auto)
        
            have "set (Lxy init {a, b}) = {a,b} \<inter> (set init)" apply(induct init)
                unfolding Lxy_def by(auto)
            with 1 have A: "set (Lxy init {a, b}) = {a,b}" by auto
            have "finite {a,b}" by auto
            from out have B: "distinct (Lxy init {a, b})" unfolding Lxy_def by auto
            have C: "length (Lxy init {a, b}) = 2"
              using distinct_card[OF B, unfolded A] using a by auto
        
            have "{xs. set xs = {a,b} \<and> distinct xs \<and> length xs =(2::nat)} 
                    = { [a,b], [b,a] }"
                  apply(auto simp: a a[symmetric])
                  proof (goal_cases)
                    case (1 xs)
                    from 1(4) obtain x xs' where r:"xs=x#xs'" by (metis Suc_length_conv add_2_eq_Suc' append_Nil length_append)
                    with 1(4) have "length xs' = 1" by auto
                    then obtain y where s: "[y] = xs'" by (metis One_nat_def length_0_conv length_Suc_conv)
                    from r s have t: "[x,y] = xs" by auto
                    moreover from t 1(1) have "x=b" using doubleton_eq_iff 1(2) by fastforce
                    moreover from t 1(1) have "y=a" using doubleton_eq_iff 1(2) by fastforce
                    ultimately show ?case by auto
                  qed
        
            with A B C have pos: "(Lxy init {a, b}) = [a,b]
                  \<or> (Lxy init {a, b}) = [b,a]" by auto
            
            show ?case
              apply(cases "(Lxy init {a, b}) = [a,b]")  
                apply(simp) using COMB_on2[OF b1 a] apply(simp)
                using pos apply(simp) unfolding twist 
              using COMB_on2[OF b2 a[symmetric]] by(simp)
          qed
    qed
next
  case 4  then show ?case using COMB_pairwise by simp
next
  case 7 then show ?case using COMB_has_finite_config_set[unfolded MTF_def, OF 7] by simp
qed (simp_all add: COMB_no_paid)



theorem COMB_competitive_nice: "compet_rand (COMB []) ((8::nat)/(5::nat)) {x::nat list. distinct x \<and> x\<noteq>[]}"
  unfolding compet_rand_def static_def using COMB_competitive by simp



end