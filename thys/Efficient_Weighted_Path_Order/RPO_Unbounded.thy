section \<open>An Unbounded Variant of RPO\<close>

text \<open>We define an unbounded version of RPO in the sense that lexicographic comparisons do not
  require a length check. This unbounded version of RPO is equivalent to the original RPO provided
  that the arities of the function symbols are below the bound that is used for lexicographic
  comparisons.\<close>

theory RPO_Unbounded
  imports
    Weighted_Path_Order.RPO
begin

fun rpo_unbounded :: "('f \<times> nat \<Rightarrow> 'f \<times> nat \<Rightarrow> bool \<times> bool) \<times> ('f \<times> nat \<Rightarrow> bool) 
  \<Rightarrow> ('f \<times> nat \<Rightarrow> order_tag) \<Rightarrow> ('f,'v)term \<Rightarrow> ('f,'v)term \<Rightarrow> bool \<times> bool" where
  "rpo_unbounded _ _ (Var x) (Var y) = (False, x = y)"
| "rpo_unbounded pr _ (Var x) (Fun g ts) = (False, ts = [] \<and> snd pr (g,0))"
| "rpo_unbounded pr c (Fun f ss) (Var y) =
    (let con = \<exists>s \<in> set ss. snd (rpo_unbounded pr c s (Var y)) in (con,con))" 
| "rpo_unbounded pr c (Fun f ss) (Fun g ts) = (
    if \<exists>s \<in> set ss. snd (rpo_unbounded pr c s (Fun g ts)) 
    then (True,True)
    else (case (fst pr) (f,length ss) (g,length ts) of (prs,prns) \<Rightarrow>
         if prns \<and> (\<forall>t \<in> set ts. fst (rpo_unbounded pr c (Fun f ss) t))
         then if prs
              then (True,True) 
              else if c (f,length ss) = c (g,length ts)
                   then if c (f,length ss) = Mul
                        then mul_ext (rpo_unbounded pr c) ss ts
                        else lex_ext_unbounded (rpo_unbounded pr c) ss ts
                   else (length ss \<noteq> 0 \<and> length ts = 0, length ts = 0)
         else (False,False)))"

lemma rpo_to_rpo_unbounded:
  assumes "\<forall> f i. (f, i) \<in> funas_term s \<union> funas_term t \<longrightarrow> i \<le> n" (is "?b s t")
  shows "rpo pr prl c n s t = rpo_unbounded (pr,prl) c s t" (is "?e s t")
proof -
  let ?p = "\<lambda> s t. ?b s t \<longrightarrow> ?e s t"
  let ?pr = "(pr,prl)" 
  {
    have "?p s t"
    proof (induct rule: rpo.induct[of _ pr prl c n])
      case (3 f ss y)    
      show ?case 
      proof (intro impI)
        assume "?b (Fun f ss) (Var y)"
        then have "\<And> s. s \<in> set ss \<Longrightarrow> ?b s (Var y)" by auto
        with 3 show "?e (Fun f ss) (Var y)" by simp
      qed
    next
      case (4 f ss g ts) note IH = this
      show ?case
      proof (intro impI)
        assume "?b (Fun f ss) (Fun g ts)"
        then have bs: "\<And> s. s \<in> set ss \<Longrightarrow> ?b s (Fun g ts)"
          and bt: "\<And> t. t \<in> set ts \<Longrightarrow> ?b (Fun f ss) t"
          and ss: "length ss \<le> n" and ts: "length ts \<le> n" by auto
        with 4(1) have s: "\<And> s. s \<in> set ss \<Longrightarrow> ?e s (Fun g ts)" by simp
        show "?e (Fun f ss) (Fun g ts)"
        proof (cases "\<exists> s \<in> set ss. snd (rpo pr prl c n s (Fun g ts))")
          case True with s show ?thesis by simp
        next
          case False note oFalse = this
          with s have oFalse2: "\<not> (\<exists>s \<in> set ss. snd (rpo_unbounded ?pr c s (Fun g ts)))"
            by simp
          obtain prns prs where Hsns: "pr (f,length ss) (g,length ts) = (prs, prns)" by force
          with bt 4(2)[OF oFalse]
          have t: "\<And> t. t \<in> set ts \<Longrightarrow> ?e (Fun f ss) t" by force
          show ?thesis
          proof (cases "prns \<and> (\<forall>t\<in>set ts. fst (rpo pr prl c n (Fun f ss) t))")
            case False
            show ?thesis
            proof (cases "prns")
              case False then show ?thesis by (simp add: oFalse oFalse2 Hsns)
            next
              case True
              with False have Hf1: "\<not> (\<forall>t\<in>set ts. fst (rpo pr prl c n (Fun f ss) t))" by simp
              with t have Hf2: "\<not> (\<forall>t\<in>set ts. fst (rpo_unbounded ?pr c (Fun f ss) t))" by auto
              show ?thesis by (simp add: oFalse oFalse2 Hf1 Hf2)
            qed         
          next
            case True
            then have prns: "prns" and Hts: "\<forall>t\<in>set ts. fst (rpo pr prl c n (Fun f ss) t)" by auto
            from Hts and t have Hts2: "\<forall>t\<in>set ts. fst (rpo_unbounded ?pr c (Fun f ss) t)" by auto
            show ?thesis
            proof (cases "prs")
              case True then show ?thesis by (simp add: oFalse oFalse2 Hsns prns Hts Hts2)
            next
              case False note prs = this
              show ?thesis
              proof (cases "c (f,length ss) = c (g,length ts)")
                case False then show ?thesis
                  by (cases "c (f,length ss)", simp_all add: oFalse oFalse2 Hsns prns Hts Hts2)
              next
                case True note cfg = this
                show ?thesis
                proof (cases "c (f,length ss)")
                  case Mul note cf = this
                  with cfg have cg: "c (g,length ts) = Mul" by simp
                  {
                    fix x y
                    assume x_in_ss: "x \<in> set ss" and y_in_ts: "y \<in> set ts"
                    have "rpo pr prl c n x y = rpo_unbounded ?pr c x y" 
                      by (rule 4(4)[OF oFalse Hsns[symmetric] refl _ prs _ conjI[OF cf cg] x_in_ss y_in_ts, rule_format],
                          insert prns Hts bs[OF x_in_ss] bt[OF y_in_ts] cf cg, auto)
                  }
                  with mul_ext_cong[of ss ss ts ts]
                  have "mul_ext (rpo pr prl c n) ss ts = mul_ext (rpo_unbounded ?pr c) ss ts"
                    by metis
                  then show ?thesis
                    by (simp add: oFalse oFalse2 Hsns prns Hts Hts2 cf cg)
                next
                  case Lex note cf = this
                  then have ncf: "c (f,length ss) \<noteq> Mul" by simp
                  from cf cfg have cg: "c (g,length ts) = Lex" by simp
                  {
                    fix i
                    assume iss: "i < length ss" and its: "i < length ts"
                    from nth_mem_mset[OF iss] and in_multiset_in_set
                    have in_ss: "ss ! i \<in> set ss" by force
                    from nth_mem_mset[OF its] and in_multiset_in_set
                    have in_ts: "ts ! i \<in> set ts" by force
                    from 4(3)[OF oFalse Hsns[symmetric] refl _ prs conjI[OF cf cg] iss its]
                      prns Hts bs[OF in_ss] bt[OF in_ts]
                    have "rpo pr prl c n (ss ! i) (ts ! i) = rpo_unbounded ?pr c (ss ! i) (ts ! i)"
                      by simp
                  }
                  with lex_ext_cong[of ss ss n n ts ts]
                  have "lex_ext (rpo pr prl c n) n ss ts
                    = lex_ext (rpo_unbounded ?pr c) n ss ts" by metis
                  then have " lex_ext (rpo pr prl c n) n ss ts = lex_ext_unbounded (rpo_unbounded ?pr c) ss ts"
                    by (simp add: lex_ext_to_lex_ext_unbounded[OF ss ts, of "rpo_unbounded ?pr c"])
                  then show ?thesis
                    by (simp add: oFalse oFalse2 Hsns prns prs Hts Hts2 cf cg)
                qed
              qed
            qed
          qed
        qed
      qed
    qed auto
  }
  then show ?thesis using assms by simp
qed

end
