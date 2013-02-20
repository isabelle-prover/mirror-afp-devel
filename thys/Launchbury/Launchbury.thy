theory Launchbury
imports Terms Heap
begin

subsubsection {* The natural semantics *}

text {* This is the semantics as in \cite{launchbury} with two exceptions:
\begin{itemize}
\item Explicit freshness requirements for bound variables in the application and the Let rule.
\item An additional parameter that stores variables that have to be avoided, but do not occur
in the judgement otherwise.
\end{itemize}
*}

inductive
  reds :: "heap \<Rightarrow> exp \<Rightarrow> var list \<Rightarrow> heap \<Rightarrow> exp \<Rightarrow> bool"
  ("_ : _ \<Down>\<^bsub>_\<^esub> _ : _" [50,50,50,50] 50)
where
  Lambda:
    "\<Gamma> : (Lam [x]. e) \<Down>\<^bsub>L\<^esub> \<Gamma> : (Lam [x]. e)" 
 | Application: "\<lbrakk>
    atom y \<sharp> (\<Gamma>,e,x,L,\<Delta>,\<Theta>,z) ;
    \<Gamma> : e \<Down>\<^bsub>x#L\<^esub> \<Delta> : (Lam [y]. e');
    \<Delta> : e'[y ::= x] \<Down>\<^bsub>L\<^esub> \<Theta> : z
  \<rbrakk>  \<Longrightarrow>
    \<Gamma> : App e x \<Down>\<^bsub>L\<^esub> \<Theta> : z" 
 | Variable: "\<lbrakk>
    (x,e) \<in> set \<Gamma>; delete x \<Gamma> : e \<Down>\<^bsub>x#L\<^esub> \<Delta> : z
  \<rbrakk> \<Longrightarrow>
    \<Gamma> : Var x \<Down>\<^bsub>L\<^esub> (x, z) # \<Delta> : z"
 | Let: "\<lbrakk>
    set (bn as) \<sharp>* (\<Gamma>, L);
    distinctVars (asToHeap as);
    asToHeap as @ \<Gamma> : body \<Down>\<^bsub>L\<^esub> \<Delta> : z
  \<rbrakk> \<Longrightarrow>
    \<Gamma> : Let as body \<Down>\<^bsub>L\<^esub> \<Delta> : z"

equivariance reds

nominal_inductive reds
  avoids Application: "y"
apply (auto simp add: fresh_star_def fresh_Pair)
done

subsubsection {* Example evaluations *}

lemma eval_test:
  "[] : (Let (ACons x (Lam [y]. Var y) ANil) (Var x)) \<Down>\<^bsub>[]\<^esub> [(x, Lam [y]. Var y)] : (Lam [y]. Var y)"
apply(auto intro!: Lambda Application Variable Let
 simp add: fresh_Pair fresh_Cons fresh_Nil fresh_star_def)
done

lemma eval_test2:
  "y \<noteq> x \<Longrightarrow> n \<noteq> y \<Longrightarrow> n \<noteq> x \<Longrightarrow>[] : (Let (ACons x (Lam [y]. Var y) ANil) (App (Var x) x)) \<Down>\<^bsub>[]\<^esub> [(x, Lam [y]. Var y)] : (Lam [y]. Var y)"
  by (auto intro!: Lambda Application Variable Let simp add: fresh_Pair fresh_at_base fresh_Cons fresh_Nil fresh_star_def)

subsubsection {* Properties of the semantics *}

text {*
Heap entries are never removed.
*}

lemma reds_doesnt_forget:
  "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z \<Longrightarrow> heapVars \<Gamma> \<subseteq> heapVars \<Delta>"
proof(induct rule: reds.induct)
case(Variable v e \<Gamma> L \<Delta> z)
  show ?case
  proof
    fix x
    assume "x \<in> heapVars \<Gamma>"
    show "x \<in> heapVars ((v, z) # \<Delta>)"
    proof(cases "x = v")
    case True 
      thus ?thesis by simp
    next
    case False
      with `x \<in> heapVars \<Gamma>`
      have "x \<in> heapVars (delete v \<Gamma>)" by simp
      hence "x \<in> heapVars \<Delta>" using Variable.hyps(3) by auto
      thus ?thesis by simp
    qed
  qed
qed (auto)

text {*
Live variables are not added to the heap.
*}

lemma reds_avoids_live:
  "\<lbrakk> \<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z;
   x \<in> set L;
   x \<notin> heapVars \<Gamma>
  \<rbrakk> \<Longrightarrow> x \<notin> heapVars \<Delta>"
proof(induct rule:reds.induct)
case (Lambda \<Gamma> x e L) thus ?case by auto
next
case (Application y \<Gamma> e x L \<Delta> \<Theta> z e') thus ?case by auto
next
case (Variable  x e \<Gamma> L \<Delta> z) thus ?case
   using heapVars_from_set[OF Variable(1)] by auto
next
case (Let as \<Gamma> L body \<Delta> z)
  have "x \<notin> heapVars \<Gamma>" by fact moreover
  have "set (bn as) \<sharp>* L" using `set (bn as) \<sharp>* (\<Gamma>, L)` by (simp add: fresh_star_Pair)
  hence "x \<notin> heapVars (asToHeap as)"
    using `x \<in> set L`
    apply -
    apply (induct as rule: asToHeap.induct)
    apply (auto simp add: exp_assn.bn_defs fresh_star_insert fresh_star_Pair)
    by (metis finite_set fresh_finite_set_at_base fresh_set)  ultimately
  have "x \<notin> heapVars (asToHeap as @ \<Gamma>)" by auto  
  thus ?case
    by (rule Let.hyps(4)[OF `x \<in> set L`])
qed

text {*
This is the same semantics with additional distinctiveness requirements. This
is defined in order to obtain a more convenient induction rule.
*}

inductive
  distinct_reds :: "heap \<Rightarrow> exp \<Rightarrow> var list \<Rightarrow> heap \<Rightarrow> exp \<Rightarrow> bool"
  ("_ : _ \<Down>d\<^bsub>_\<^esub> _ : _" [50,50,50,50] 50)
where
  DLambda:
    "distinctVars \<Gamma> \<Longrightarrow> \<Gamma> : (Lam [x]. e) \<Down>d\<^bsub>L\<^esub> \<Gamma> : (Lam [x]. e)" 
 | DApplication: "\<lbrakk>
    atom y \<sharp> (\<Gamma>,e,x,L,\<Delta>,\<Theta>,z) ;
    \<Gamma> : e \<Down>d\<^bsub>x#L\<^esub> \<Delta> : (Lam [y]. e');
    \<Delta> : e'[y ::= x] \<Down>d\<^bsub>L\<^esub> \<Theta> : z;
    distinctVars \<Gamma>;
    distinctVars \<Theta>
  \<rbrakk>  \<Longrightarrow>
    \<Gamma> : App e x \<Down>d\<^bsub>L\<^esub> \<Theta> : z" 
 | DVariable: "\<lbrakk>
    (x,e) \<in> set \<Gamma>;
    delete x \<Gamma> : e \<Down>d\<^bsub>x#L\<^esub> \<Delta> : z;
    distinctVars \<Gamma>;
    distinctVars ((x,z) # \<Delta>)
  \<rbrakk> \<Longrightarrow>
    \<Gamma> : Var x \<Down>d\<^bsub>L\<^esub> (x, z) # \<Delta> : z"
 | DLet: "\<lbrakk>
    set (bn as) \<sharp>* (\<Gamma>, L);
    distinctVars (asToHeap as);
    asToHeap as @ \<Gamma> : body \<Down>d\<^bsub>L\<^esub> \<Delta> : z;
    distinctVars \<Gamma>;
    distinctVars \<Delta>
  \<rbrakk> \<Longrightarrow>
    \<Gamma> : Let as body \<Down>d\<^bsub>L\<^esub> \<Delta> : z"

equivariance distinct_reds

nominal_inductive distinct_reds
  avoids DApplication: "y"
  apply (auto simp add: fresh_star_def fresh_Cons fresh_Pair)
  done

lemma distinct_redsD1:
  "\<Gamma> : e \<Down>d\<^bsub>L\<^esub> \<Delta> : z \<Longrightarrow> \<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z"
  apply (nominal_induct rule: distinct_reds.strong_induct)
  apply (auto intro:reds.intros simp add: fresh_star_Pair fresh_Pair)
  done

lemma distinct_redsD2:
  "\<Gamma> : e \<Down>d\<^bsub>L\<^esub> \<Delta> : z \<Longrightarrow> distinctVars \<Gamma>"
  apply (nominal_induct rule: distinct_reds.strong_induct)
  apply (auto)
  done

lemma distinct_redsD3:
  "\<Gamma> : e \<Down>d\<^bsub>L\<^esub> \<Delta> : z \<Longrightarrow> distinctVars \<Delta>"
  apply (nominal_induct rule: distinct_reds.strong_induct)
  apply (auto)
  done


lemma distinct_redsI:
  "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z \<Longrightarrow> distinctVars \<Gamma> \<Longrightarrow> \<Gamma> : e \<Down>d\<^bsub>L\<^esub> \<Delta> : z"
proof (nominal_induct rule: reds.strong_induct)
  case (Variable x e \<Gamma> L \<Delta> z)
    have "x \<notin> heapVars \<Delta>"
      apply (rule reds_avoids_live[OF Variable(2)])
      apply (auto)
      done
    moreover
    have "distinctVars (delete x \<Gamma>)"
      by (rule distinctVars_delete[OF Variable(4)])
    hence "delete x \<Gamma> : e \<Down>d\<^bsub>x # L\<^esub> \<Delta> : z" by (rule Variable.hyps)
    moreover
    hence "distinctVars \<Delta>" by (rule distinct_redsD3)
    hence "distinctVars ((x, z) # \<Delta>)"
      using `x \<notin> heapVars \<Delta>` by (simp add: distinctVars_Cons)
    ultimately
    show ?case
      using Variable
      by (metis distinct_reds.DVariable)
qed (auto intro: distinctVars_append_asToHeap dest: distinct_redsD3 intro!: distinct_reds.intros simp add: fresh_star_Pair)

lemma reds_pres_distinctVars:
  "\<Gamma> : \<Gamma>' \<Down>\<^bsub>L\<^esub> \<Delta> : \<Delta>' \<Longrightarrow> distinctVars \<Gamma> \<Longrightarrow> distinctVars \<Delta>"
by (metis distinct_redsD3 distinct_redsI)

lemmas reds_distinct_ind = distinct_reds.induct[OF distinct_redsI, consumes 2, case_names Lambda Application Variable Let]
lemmas reds_distinct_strong_ind = distinct_reds.strong_induct[OF distinct_redsI, consumes 2, case_names Lambda Application Variable Let]

text {*
Fresh variables either stay fresh or are added to the heap.
*}

lemma reds_fresh:" \<lbrakk> \<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z;
   atom (x::var) \<sharp> (\<Gamma>, e)
  \<rbrakk> \<Longrightarrow> atom x \<sharp> (\<Delta>, z) \<or> x \<in> (heapVars \<Delta> - set L)"
proof(induct rule: reds.induct)
case (Lambda \<Gamma> x e) thus ?case by auto
next
case (Application y \<Gamma> e x' L \<Delta> \<Theta> z e')
  hence "atom x \<sharp> (\<Delta>, Lam [y]. e') \<or> x \<in> heapVars \<Delta> - set (x' # L)" by (auto simp add: fresh_Pair)

  thus ?case
  proof
    assume  "atom x \<sharp> (\<Delta>, Lam [y]. e')"
    show ?thesis
    proof(cases "x = y")
    case False
      hence "atom x \<sharp> e'" using `atom x \<sharp> (\<Delta>, Lam [y]. e')`
        by (auto simp add:fresh_Pair)
      hence "atom x \<sharp> e'[y ::= x']" using Application.prems
        by (auto intro: subst_pres_fresh[rule_format] simp add: fresh_Pair)
      thus ?thesis using Application.hyps(5) `atom x \<sharp> (\<Delta>, Lam [y]. e')` by auto
    next
    case True
      hence "atom x \<sharp> e'[y ::= x']" using `atom x \<sharp> (\<Delta>, Lam [y]. e')` Application.prems
        by (auto intro:subst_is_fresh simp add: fresh_Pair)
      thus ?thesis using Application.hyps(5) `atom x \<sharp> (\<Delta>, Lam [y]. e')` by auto
    qed
  next
    assume "x \<in> heapVars \<Delta>  - set (x' # L)"
    thus ?thesis using reds_doesnt_forget[OF Application.hyps(4)] by auto
  qed
next

case(Variable v e \<Gamma> L \<Delta> z)
  have "atom x \<sharp> \<Gamma>" and "atom x \<sharp> v" using Variable.prems(1) by (auto simp add: fresh_Pair)
  hence "atom x \<sharp> delete v \<Gamma>" and "atom x \<sharp> e" using `(v,e) \<in> set \<Gamma>` by(auto intro: fresh_delete dest:fresh_list_elem)
  hence "atom x \<sharp> (\<Delta>, z) \<or> x \<in> heapVars \<Delta> - set (v # L)"  using Variable.hyps(3) by (auto simp add: fresh_Pair)
  thus ?case using `atom x \<sharp> v` by (auto simp add: fresh_Pair fresh_Cons fresh_at_base)
next

case (Let as \<Gamma> L body \<Delta> z)
  show ?case
    proof (cases "atom x \<in> set(bn as)")
    case False
      hence "atom x \<sharp> as" using Let.prems by(auto simp add: fresh_Pair)      
      hence "atom x \<sharp> asToHeap as"
        by(induct as rule:asToHeap.induct)(auto simp add: fresh_Nil fresh_Cons fresh_Pair)
      show ?thesis
        apply(rule Let.hyps(4))
        using Let.prems `atom x \<sharp> asToHeap as` False
        by (auto simp add: fresh_Pair fresh_append)
    next
    case True
      hence "x \<in> heapVars (asToHeap as)" 
        by(induct as rule:asToHeap.induct)(auto simp add: exp_assn.bn_defs)      
      moreover
      have "x \<notin> set L"
        using Let(1)
        by (metis True fresh_list_elem fresh_star_Pair fresh_star_def not_self_fresh)
      ultimately
      show ?thesis
      using reds_doesnt_forget[OF Let.hyps(3)] by auto
    qed
qed

text {*
Reducing the set of variables to avoid is always possible.
*} 

lemma reds_smaller_L: "\<lbrakk> \<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z;
   set L' \<subseteq> set L
  \<rbrakk> \<Longrightarrow> \<Gamma> : e \<Down>\<^bsub>L'\<^esub> \<Delta> : z"
proof(nominal_induct avoiding : L' rule: reds.strong_induct)
case (Lambda \<Gamma> x e L L')
  show ?case
    by (rule reds.Lambda)
next
case (Application y \<Gamma> e xa L \<Delta> \<Theta> z e' L')
  show ?case
  proof(rule reds.Application)
    show "atom y \<sharp> (\<Gamma>, e, xa, L', \<Delta>, \<Theta>, z)"
      using Application
      by (auto simp add: fresh_Pair)
  
    have "set (xa # L') \<subseteq> set (xa # L)"
      using `set L' \<subseteq> set L` by auto
    thus "\<Gamma> : e \<Down>\<^bsub>xa # L'\<^esub> \<Delta> : Lam [y]. e'"
      by (rule Application.hyps(10))

    show "\<Delta> : e'[y::=xa] \<Down>\<^bsub>L'\<^esub> \<Theta> : z "
      by (rule Application.hyps(12)[OF Application.prems])
  qed
next 
case (Variable xa e \<Gamma> L \<Delta> z L')
  have "set (xa # L') \<subseteq> set (xa # L)"
    using Variable.prems by auto
  thus ?case
    by (rule reds.Variable[OF Variable(1) Variable.hyps(3)])
next
case (Let as \<Gamma>  L body \<Delta> z L')
  have "set (bn as) \<sharp>* (\<Gamma>, L')"
    using Let(1-3) Let.prems
    by (auto simp add: fresh_star_Pair  fresh_star_set_subset)
  thus ?case
    by (rule reds.Let[OF _ Let.hyps(3) Let.hyps(5)[OF Let.prems]])
qed
end

