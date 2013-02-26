theory CorrectnessStacked
  imports "Denotational-Props" LaunchburyStacked
begin

text {* This is the main correctness theorem for the stacked semantics. *}

theorem correctness:
  assumes "\<Gamma> : \<Gamma>' \<Down> \<Delta> : \<Delta>'"
  and "distinctVars (\<Gamma>' @ \<Gamma>)"
  shows "\<lbrace>\<Gamma>'@\<Gamma>\<rbrace> \<le> \<lbrace>\<Delta>'@\<Delta>\<rbrace>"
  using assms
proof(induct rule:reds_distinct_ind)

case (Lambda x y e \<Gamma> \<Gamma>')
  show ?case by simp
  -- "The lambda-case is trival"
next

case (Application n \<Gamma> \<Gamma>' \<Delta> \<Delta>' x e y \<Theta> \<Theta>' z  e')
  let "?restr \<rho>" = "fmap_restr (insert x (heapVars \<Gamma>' \<union> heapVars \<Gamma>)) (\<rho>::Env)"
  let "?restr2 \<rho>" = "fmap_restr (insert x (heapVars \<Delta>' \<union> heapVars \<Delta>)) (\<rho>::Env)"

  have "n \<noteq> z" using Application by (simp add: fresh_Pair fresh_at_base)

  from stack_unchanged[OF distinct_redsD1[OF Application.hyps(8)]]
  have "\<Delta>' = \<Gamma>'" by simp
  hence [simp]:"atom n \<sharp> \<Delta>'"  using Application by (simp add: fresh_Pair)+
  
  have "atom n \<sharp> (\<Gamma>, e)" using Application by (simp add: fresh_Pair)
  note reds_fresh[OF Application(8) this]
  hence "atom n \<sharp> (\<Delta>, Lam [z]. e')"
    using Application(5)
    by (metis (hide_lams, no_types) Application(1) fresh_Pair heapVars_not_fresh)
  with `n \<noteq> z`
  have [simp]: "atom n \<sharp> \<Delta>" "atom n \<sharp> e'"
    by (auto simp add: fresh_Pair)

  note subset1 = reds_doesnt_forget'(1)[OF Application.hyps(8), unfolded append_Cons]
  from reds_doesnt_forget'(2)[OF Application.hyps(8), unfolded append_Cons]
  have subset2: "heapVars ((x, App (Var n) y) # \<Gamma>') \<subseteq> heapVars ((x, App (Var n) y) # \<Delta>')"
    apply (rule distinctVars_Cons_subset)
    apply (metis Application(4) distinctVars_appendD1)
    apply (metis Application(5) distinctVars_appendD1)
    done

  have "n \<noteq> x" 
    by (metis Application(1) fresh_PairD(1) fresh_PairD(2) not_self_fresh)

  have "\<lbrace>((x, App e y) # \<Gamma>') @ \<Gamma>\<rbrace> = (\<lbrace>(x, App e y) # \<Gamma>' @ \<Gamma>\<rbrace>)"
    by simp
  also
  have "... = ?restr (\<lbrace>(n, e) # (x, App e y) # \<Gamma>' @ \<Gamma>\<rbrace>)"
    -- {* Adding a fresh variable *}
    apply (subst HSem_add_fresh[of fempty "(x, App e y) # \<Gamma>' @ \<Gamma>" n e, symmetric])
    apply (rule fempty_is_HSem_cond)
    apply (rule fempty_is_HSem_cond)
    using Application(1) apply (simp add: fresh_Pair fresh_Cons fresh_append)
    apply simp
    done
  also have  "... = ?restr (\<lbrace>(x, App e y) # (n, e) # \<Gamma>' @ \<Gamma>\<rbrace>)"
    by (rule arg_cong[OF HSem_reorder_head[OF `n \<noteq> x`]])
  also
  have "... = ?restr (\<lbrace>(x, App (Var n) y) # (n, e) # \<Gamma>' @ \<Gamma>\<rbrace>)"
    -- {* Substituting the variable *}
    apply (rule arg_cong[OF HSem_subst_var_app[symmetric]])
    apply (rule fempty_is_HSem_cond)
    apply (rule fempty_is_HSem_cond)
    using Application(1) apply (simp add: fresh_Pair)
    done
  also
  have "... = ?restr (\<lbrace>(n, e) # (x, App (Var n) y) # \<Gamma>' @ \<Gamma>\<rbrace>)"
    by (simp add: HSem_reorder_head[OF `n \<noteq> x`])
  also
  have "... \<le> ?restr2  (\<lbrace>(n, Lam [z]. e') # (x, App (Var n) y) # \<Delta>' @ \<Delta>\<rbrace>)"
    -- "Induction hypothesis"
    apply (rule fmap_restr_le[OF Application.hyps(9)[simplified]])
    using subset1 subset2 by auto
  also
  have "... \<le> ?restr2  (\<lbrace>(x, App (Var n) y) # (n, Lam [z]. e') # \<Delta>' @ \<Delta>\<rbrace>)"
    by (simp add: HSem_reorder_head[OF `n \<noteq> x`])
  also
  have "... = ?restr2 (\<lbrace>(x, App (Lam [z]. e') y) # (n, Lam [z]. e') # \<Delta>' @ \<Delta>\<rbrace>)"
    -- "Substituting the variable again"
    apply (rule arg_cong[OF HSem_subst_var_app])
    apply (rule fempty_is_HSem_cond)
    apply (rule fempty_is_HSem_cond)
    using Application(1) apply (simp add: fresh_Pair)
    done
  also
  have "... = ?restr2 (\<lbrace>(n, Lam [z]. e') # (x, App (Lam [z]. e') y) # \<Delta>' @ \<Delta>\<rbrace>)"
    by (simp add: HSem_reorder_head[OF `n \<noteq> x`])
  also
  have "... = (\<lbrace>(x, App (Lam [z]. e') y) # \<Delta>' @ \<Delta>\<rbrace>)"
    -- "Removing the fresh variable"
    apply (subst HSem_add_fresh[of fempty "(x, App (Lam [z]. e') y) # \<Delta>' @ \<Delta>" n "Lam [z]. e'", symmetric])
    apply (rule fempty_is_HSem_cond)
    apply (rule fempty_is_HSem_cond)
    using Application(1) apply (simp add: fresh_Pair fresh_Cons fresh_append)
    apply simp
    done
  also
  have "... =  \<lbrace>(x, e'[z::=y]) # \<Delta>' @ \<Delta>\<rbrace>"
    -- "Semantics of application"
    apply (rule HSem_subst_exp[OF fempty_is_HSem_cond fempty_is_HSem_cond])
    apply (simp)
    apply (subgoal_tac "atom z \<sharp> \<rho>'")
    apply (subst ESem.simps, assumption)
    apply simp
    apply (rule ESem_subst[simplified])
      using Application(2)
      apply (auto simp add: sharp_Env fresh_Pair heapVars_not_fresh)
    done
  also
  have "... \<le> \<lbrace>\<Theta>' @ \<Theta>\<rbrace>"
    -- "Induction hypothesis"
    by (rule Application.hyps(11)[simplified])
  finally
  show "\<lbrace>((x, App e y) # \<Gamma>') @ \<Gamma>\<rbrace> \<le> \<lbrace>\<Theta>' @ \<Theta>\<rbrace>".

next
case (Variable y e \<Gamma> x \<Gamma>' z \<Delta>' \<Delta>)
  have "x \<noteq> y"
    using Variable(3) by (auto simp add: distinctVars_Cons distinctVars_append)
  have "distinctVars \<Gamma>"
    using Variable(2) by (auto simp add: distinctVars_Cons distinctVars_append)
  have d2: "distinctVars (((y, z) # (x, z) # \<Delta>') @ \<Delta>)"
    using Variable.hyps(4)
    by (simp add: distinctVars_append distinctVars_Cons)

  have "\<lbrace>((x, Var y) # \<Gamma>') @ \<Gamma>\<rbrace> = \<lbrace>((y, e) # (x, Var y) # \<Gamma>') @ delete y \<Gamma>\<rbrace>"
    apply (rule HSem_reorder[OF Variable.hyps(2,3)])
    using distinctVars_set_delete_insert[OF `distinctVars \<Gamma>` Variable(1)]
    by auto
  also
  have "... \<le>  \<lbrace>((y, z) # (x, Var y) # \<Delta>') @ \<Delta>\<rbrace>"
    -- "Induction hypothesis"
    by fact
  also
  have "... =  \<lbrace>(y, z) # (x, Var y) # \<Delta>' @ \<Delta>\<rbrace>"
    by simp
  also
  have "... =  \<lbrace>(x, Var y) # (y, z) # \<Delta>' @ \<Delta>\<rbrace>"
    by (simp add: HSem_reorder_head[OF `x \<noteq> y`])
  also
  have "... =  \<lbrace>(x, z) # (y, z) # \<Delta>' @ \<Delta>\<rbrace>"
    -- {* Substituting the variable @{term y} *}
    apply (rule HSem_subst_var_var)
    apply (rule fempty_is_HSem_cond)
    apply (rule fempty_is_HSem_cond)
    using `x \<noteq> y` by (simp add: fresh_Pair fresh_at_base)
  also
  have "... =  \<lbrace>(y, z) # (x, z) # \<Delta>' @ \<Delta>\<rbrace>"
    by (simp add: HSem_reorder_head[OF `x \<noteq> y`])
  also
  have "... =  \<lbrace>((y, z) # (x, z) # \<Delta>') @ \<Delta>\<rbrace>"
    by simp
  also
  have "... = \<lbrace>((x, z) # \<Delta>') @ (y, z) # \<Delta>\<rbrace>"
    -- "Induction hypothesis"
    by (rule HSem_reorder[OF d2 Variable.hyps(5)], auto)
  finally
  show "\<lbrace>((x, Var y) # \<Gamma>') @ \<Gamma>\<rbrace> \<le> \<lbrace>((x, z) # \<Delta>') @ (y, z) # \<Delta>\<rbrace>".

next
case (Let as \<Gamma> x \<Gamma>' body \<Delta>' \<Delta>)
  have "distinctVars (asToHeap as @ ((x, Terms.Let as body) # \<Gamma>') @ \<Gamma>)"
    by (metis Let(1) Let(2) Let(3) distinctVars_append_asToHeap fresh_star_Cons fresh_star_Pair fresh_star_append let_binders_fresh)
  hence d3: "distinctVars ((x, body) # asToHeap as @ \<Gamma>' @ \<Gamma>)"
    and d4: "distinctVars (((x, body) # \<Gamma>') @ asToHeap as @ \<Gamma>)"
    and d5: "distinctVars ((x, body) # \<Gamma>' @ \<Gamma>)"
    by (auto simp add: distinctVars_Cons distinctVars_append)

  have "\<lbrace>((x, Let as body) # \<Gamma>') @ \<Gamma>\<rbrace> = \<lbrace>(x, Let as body) # \<Gamma>' @ \<Gamma>\<rbrace>"
    by simp
  also
  have "... \<le> \<lbrace>(x, body) # asToHeap as @ \<Gamma>' @ \<Gamma>\<rbrace>"
    -- "Semantics of let"
    apply (rule HSem_unfold_let[OF fempty_is_HSem_cond fempty_is_HSem_cond fempty_is_HSem_cond Let(2) d5 _ refl])
    using Let(1) by (auto simp add: fresh_star_Pair fresh_star_append)[1]
  also
  have "... = \<lbrace>((x, body) # \<Gamma>') @ asToHeap as @ \<Gamma>\<rbrace>"
     by (rule HSem_reorder[OF d3 d4], auto)
  also
  have "... \<le>  \<lbrace>\<Delta>' @ \<Delta>\<rbrace>"
    -- "Induction hypothesis"
    by fact
  finally
  show "\<lbrace>((x, Terms.Let as body) # \<Gamma>') @ \<Gamma>\<rbrace> \<le> \<lbrace>\<Delta>' @ \<Delta>\<rbrace>".
qed
end

