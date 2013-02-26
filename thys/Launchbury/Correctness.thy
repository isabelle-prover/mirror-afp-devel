theory Correctness
  imports "CorrectnessStacked" "Launchbury-Unstack"
begin

text {*
As a corollary of the correctness of the stacked semantics and its equivalence to the original
semantics we obtaim Theorem 2 from \cite{launchbury}.
*}

theorem correctness:
  assumes "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z"
  and [simp]:"distinctVars \<Gamma>"
  shows "\<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<^esub> = \<lbrakk>z\<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<^esub>" and "\<lbrace>\<Gamma>\<rbrace> \<le> \<lbrace>\<Delta>\<rbrace>"
proof-
  obtain x :: var where fresh: "atom x \<sharp> (\<Gamma>,e,\<Delta>,z)"
    by (rule obtain_fresh)

  have "\<Gamma> : e \<Down>\<^bsub>x#L\<^esub> \<Delta> : z"
    by (rule reds_add_var_L[OF assms(1) fresh], simp)
  hence "\<Gamma> : [(x, e)] \<Down> \<Delta> : [(x, z)]"
    by (rule add_stack, simp_all add: supp_Nil)
  moreover
  from fresh
  have "x \<notin> heapVars \<Gamma>"
    by (metis heapVars_not_fresh fresh_Pair)
  hence "distinctVars ([(x, e)] @ \<Gamma>)"
    by (simp add: distinctVars_append distinctVars_Cons)
  ultimately
  have le: "\<lbrace>[(x, e)] @ \<Gamma>\<rbrace> \<le> \<lbrace>[(x, z)] @ \<Delta>\<rbrace>"
    by (rule CorrectnessStacked.correctness)

  have "\<lbrace>\<Gamma>\<rbrace> = fmap_restr (heapVars \<Gamma>) (\<lbrace>(x, e) # \<Gamma>\<rbrace>)"
    apply (rule HSem_add_fresh[OF fempty_is_HSem_cond fempty_is_HSem_cond, simplified (no_asm), symmetric])
    using fresh apply (simp add: fresh_Pair)
    done
  also have "... \<le> fmap_restr (heapVars \<Delta>) (\<lbrace>(x, z) # \<Delta>\<rbrace>)"
    by (rule fmap_restr_le[OF le Launchbury.reds_doesnt_forget[OF assms(1)], simplified])
  also have "... = \<lbrace>\<Delta>\<rbrace>"
    apply (rule HSem_add_fresh[OF fempty_is_HSem_cond fempty_is_HSem_cond, simplified (no_asm)])
    using fresh apply (simp add: fresh_Pair)
    done
  finally show "\<lbrace>\<Gamma>\<rbrace> \<le> \<lbrace>\<Delta>\<rbrace>".

  have "\<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<^esub> = \<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>(x, e) # \<Gamma>\<rbrace>\<^esub>"
    apply (rule ESem_add_fresh[OF fempty_is_HSem_cond fempty_is_HSem_cond, symmetric])
    using fresh by (simp add: fresh_Pair)
  also have "... = \<lbrace>(x, e) # \<Gamma>\<rbrace> f! x"
    apply (rule the_lookup_HSem_heap[of _ "(x, e) # \<Gamma>" x, simplified (no_asm), symmetric])
    apply (rule fempty_is_HSem_cond)
    apply simp_all    
    done
  also have "... = \<lbrace>(x, z) # \<Delta>\<rbrace> f! x"
    apply (rule arg_cong[OF fmap_less_eqD[OF le, simplified]])
    apply simp
    done
  also have "... = \<lbrakk>z\<rbrakk>\<^bsub>\<lbrace>(x, z) # \<Delta>\<rbrace>\<^esub>"
    apply (rule the_lookup_HSem_heap[of _ "(x, z) # \<Delta>" x, OF fempty_is_HSem_cond, simplified (no_asm)])
    apply simp_all    
    done
  also have "... =  \<lbrakk>z\<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<^esub>"
    apply (rule ESem_add_fresh[OF fempty_is_HSem_cond fempty_is_HSem_cond])
    using fresh by (simp add: fresh_Pair)
  finally show "\<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<^esub> = \<lbrakk> z \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<^esub>".
qed
end
