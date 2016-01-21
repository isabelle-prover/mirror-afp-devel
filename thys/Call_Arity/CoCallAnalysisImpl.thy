theory CoCallAnalysisImpl
imports "Arity-Nominal" "../Launchbury/Nominal-HOLCF" "../Launchbury/Env-Nominal"  "Env-Set-Cpo" "../Launchbury/Env-HOLCF" CoCallFix
begin

fun combined_restrict :: "var set \<Rightarrow> (AEnv \<times> CoCalls) \<Rightarrow> (AEnv \<times> CoCalls)"
  where "combined_restrict S (env, G) = (env f|` S, cc_restr S G)"

lemma fst_combined_restrict[simp]:
  "fst (combined_restrict S p) = fst p f|` S"
  by (cases p, simp)

lemma snd_combined_restrict[simp]:
  "snd (combined_restrict S p) = cc_restr S (snd p)"
  by (cases p, simp)

lemma combined_restrict_eqvt[eqvt]:
  shows "\<pi> \<bullet> combined_restrict S p = combined_restrict (\<pi> \<bullet> S) (\<pi> \<bullet> p)"
  by (cases p) auto

lemma combined_restrict_cont:
  "cont (\<lambda>x. combined_restrict S x)"
proof-
  have "cont (\<lambda>(env, G). combined_restrict S (env, G))" by simp
  then show ?thesis by (simp only: case_prod_eta) 
qed
lemmas cont_compose[OF combined_restrict_cont, cont2cont, simp]

lemma combined_restrict_perm:
  assumes "supp \<pi> \<sharp>* S" and [simp]: "finite S"
  shows "combined_restrict S (\<pi> \<bullet> p) = combined_restrict S p"
proof(cases p)
  fix env :: AEnv and  G :: CoCalls
  assume "p = (env, G)"
  moreover 
  from assms
  have "env_restr S (\<pi> \<bullet> env) = env_restr S env" by (rule env_restr_perm)
  moreover
  from assms
  have "cc_restr S (\<pi> \<bullet> G) = cc_restr S G" by (rule cc_restr_perm)
  ultimately
  show ?thesis by simp
qed

definition predCC :: "var set \<Rightarrow> (Arity \<rightarrow> CoCalls) \<Rightarrow> (Arity \<rightarrow> CoCalls)"
  where "predCC S f = (\<Lambda> a. if a \<noteq> 0 then cc_restr S (f\<cdot>(pred\<cdot>a)) else ccSquare S)"

lemma predCC_eq:
  shows "predCC S f \<cdot> a = (if a \<noteq> 0 then cc_restr S (f\<cdot>(pred\<cdot>a)) else ccSquare S)"
  unfolding predCC_def
  apply (rule beta_cfun)
  apply (rule cont_if_else_above)
  apply (auto dest: set_mp[OF ccField_cc_restr])
  done

lemma predCC_eqvt[eqvt, simp]: "\<pi> \<bullet> (predCC S f) = predCC (\<pi> \<bullet> S) (\<pi> \<bullet> f)"
  apply (rule cfun_eqvtI)
  unfolding predCC_eq
  by perm_simp rule

lemma cc_restr_predCC:
  "cc_restr S (predCC S' f\<cdot>n) = (predCC (S' \<inter> S) (\<Lambda> n. cc_restr S (f\<cdot>n)))\<cdot>n"
  unfolding predCC_eq
  by (auto simp add: inf_commute ccSquare_def)

lemma cc_restr_predCC'[simp]:
  "cc_restr S (predCC S f\<cdot>n) = predCC S f\<cdot>n"
  unfolding predCC_eq by simp

  
nominal_function
  cCCexp :: "exp \<Rightarrow> (Arity \<rightarrow> AEnv \<times> CoCalls)" 
where
  "cCCexp (Var x) =      (\<Lambda> n . (esing x \<cdot> (up \<cdot> n),                                   \<bottom>))"
| "cCCexp (Lam [x]. e) = (\<Lambda> n . combined_restrict (fv (Lam [x]. e)) (fst (cCCexp e\<cdot>(pred\<cdot>n)), predCC (fv (Lam [x]. e)) (\<Lambda> a. snd(cCCexp e\<cdot>a))\<cdot>n))"
| "cCCexp (App e x) =    (\<Lambda> n . (fst (cCCexp e\<cdot>(inc\<cdot>n)) \<squnion> (esing x \<cdot> (up\<cdot>0)),          snd (cCCexp e\<cdot>(inc\<cdot>n)) \<squnion> ccProd {x} (insert x (fv e))))"
| "cCCexp (Let \<Gamma> e) =    (\<Lambda> n . combined_restrict (fv (Let \<Gamma> e)) (CoCallArityAnalysis.cccFix_choose cCCexp \<Gamma> \<cdot> (cCCexp e\<cdot>n)))"
| "cCCexp (Bool b) =     \<bottom>"
| "cCCexp (scrut ? e1 : e2) = (\<Lambda> n. (fst (cCCexp scrut\<cdot>0) \<squnion> fst (cCCexp e1\<cdot>n) \<squnion> fst (cCCexp e2\<cdot>n),
     snd (cCCexp scrut\<cdot>0) \<squnion> (snd (cCCexp e1\<cdot>n) \<squnion> snd (cCCexp e2\<cdot>n)) \<squnion> ccProd (edom (fst (cCCexp scrut\<cdot>0))) (edom (fst (cCCexp e1\<cdot>n)) \<union> edom (fst (cCCexp e2\<cdot>n)))))"
proof goal_cases
  case 1
  show ?case
    unfolding eqvt_def cCCexp_graph_aux_def
    apply rule
    apply (perm_simp)
    apply (simp add: Abs_cfun_eqvt)
    done
next
  case 3
  thus ?case by (metis Terms.exp_strong_exhaust)
next
  case prems: (10 x e x' e')
  from prems(9)
  show ?case
  proof(rule eqvt_lam_case)
    fix \<pi> :: perm
    assume *: "supp (-\<pi>) \<sharp>* (fv (Lam [x]. e) :: var set)" 
    {
    fix n
    have "combined_restrict (fv (Lam [x]. e)) (fst (cCCexp_sumC (\<pi> \<bullet> e)\<cdot>(pred\<cdot>n)), predCC (fv (Lam [x]. e)) (\<Lambda> a. snd(cCCexp_sumC (\<pi> \<bullet> e)\<cdot>a))\<cdot>n)
       = combined_restrict (fv (Lam [x]. e)) (- \<pi> \<bullet> (fst (cCCexp_sumC (\<pi> \<bullet> e)\<cdot>(pred\<cdot>n)), predCC (fv (Lam [x]. e)) (\<Lambda> a. snd(cCCexp_sumC (\<pi> \<bullet> e)\<cdot>a))\<cdot>n))"
      by (rule combined_restrict_perm[symmetric, OF *]) simp
    also have "\<dots> = combined_restrict (fv (Lam [x]. e)) (fst (cCCexp_sumC e\<cdot>(pred\<cdot>n)), predCC (- \<pi> \<bullet> fv (Lam [x]. e)) (\<Lambda> a. snd(cCCexp_sumC e\<cdot>a))\<cdot>n)"
      by (perm_simp, simp add: eqvt_at_apply[OF prems(1)] pemute_minus_self Abs_cfun_eqvt)
    also have "- \<pi> \<bullet> fv (Lam [x]. e) = (fv (Lam [x]. e) :: var set)" by (rule perm_supp_eq[OF *])
    also note calculation
    }
    thus "(\<Lambda> n. combined_restrict (fv (Lam [x]. e)) (fst (cCCexp_sumC (\<pi> \<bullet> e)\<cdot>(pred\<cdot>n)), predCC (fv (Lam [x]. e)) (\<Lambda> a. snd(cCCexp_sumC (\<pi> \<bullet> e)\<cdot>a))\<cdot>n))
        = (\<Lambda> n. combined_restrict (fv (Lam [x]. e)) (fst (cCCexp_sumC e\<cdot>(pred\<cdot>n)), predCC (fv (Lam [x]. e)) (\<Lambda> a. snd(cCCexp_sumC e\<cdot>a))\<cdot>n))" by simp
  qed
next
  case prems: (19 \<Gamma> body \<Gamma>' body')
  from prems(9)
  show ?case
  proof (rule eqvt_let_case)
    fix \<pi> :: perm
    assume *: "supp (-\<pi>) \<sharp>* (fv (Terms.Let \<Gamma> body) :: var set)"
    
    { fix n
      have "combined_restrict (fv (Terms.Let \<Gamma> body)) (CoCallArityAnalysis.cccFix_choose cCCexp_sumC (\<pi> \<bullet> \<Gamma>)\<cdot>(cCCexp_sumC (\<pi> \<bullet> body)\<cdot>n))
      =  combined_restrict (fv (Terms.Let \<Gamma> body)) (- \<pi> \<bullet> (CoCallArityAnalysis.cccFix_choose cCCexp_sumC (\<pi> \<bullet> \<Gamma>)\<cdot>(cCCexp_sumC (\<pi> \<bullet> body)\<cdot>n)))"
        by (rule combined_restrict_perm[OF *, symmetric]) simp
      also have "- \<pi> \<bullet> (CoCallArityAnalysis.cccFix_choose cCCexp_sumC (\<pi> \<bullet> \<Gamma>)\<cdot>(cCCexp_sumC (\<pi> \<bullet> body)\<cdot>n)) = 
                       CoCallArityAnalysis.cccFix_choose (- \<pi> \<bullet> cCCexp_sumC) \<Gamma>\<cdot>((- \<pi> \<bullet> cCCexp_sumC) body\<cdot>n)"
        by (simp add: pemute_minus_self)
      also have "CoCallArityAnalysis.cccFix_choose (- \<pi> \<bullet> cCCexp_sumC) \<Gamma> = CoCallArityAnalysis.cccFix_choose cCCexp_sumC \<Gamma>"
        by (rule cccFix_choose_cong[OF eqvt_at_apply[OF prems(1)] refl])
      also have "(- \<pi> \<bullet> cCCexp_sumC) body = cCCexp_sumC body"
        by (rule eqvt_at_apply[OF prems(2)])
      also note calculation
    }
    thus "(\<Lambda> n. combined_restrict (fv (Terms.Let \<Gamma> body)) (CoCallArityAnalysis.cccFix_choose cCCexp_sumC (\<pi> \<bullet> \<Gamma>)\<cdot>(cCCexp_sumC (\<pi> \<bullet> body)\<cdot>n))) =
         (\<Lambda> n. combined_restrict (fv (Terms.Let \<Gamma> body)) (CoCallArityAnalysis.cccFix_choose cCCexp_sumC \<Gamma>\<cdot>(cCCexp_sumC body\<cdot>n)))" by (simp only:)
  qed
qed auto

nominal_termination (eqvt) by lexicographic_order

locale CoCallAnalysisImpl
begin
sublocale CoCallArityAnalysis cCCexp.
sublocale ArityAnalysis Aexp.

lemma cCCexp_eq[simp]:
  "cCCexp (Var x)\<cdot>n =      (esing x \<cdot> (up \<cdot> n),                                   \<bottom>)"
  "cCCexp (Lam [x]. e)\<cdot>n = combined_restrict (fv (Lam [x]. e)) (fst (cCCexp e\<cdot>(pred\<cdot>n)), predCC (fv (Lam [x]. e)) (\<Lambda> a. snd(cCCexp e\<cdot>a))\<cdot>n)"
  "cCCexp (App e x)\<cdot>n =    (fst (cCCexp e\<cdot>(inc\<cdot>n)) \<squnion> (esing x \<cdot> (up\<cdot>0)),          snd (cCCexp e\<cdot>(inc\<cdot>n)) \<squnion> ccProd {x} (insert x (fv e)))"
  "cCCexp (Let \<Gamma> e)\<cdot>n =    combined_restrict (fv (Let \<Gamma> e)) (CoCallArityAnalysis.cccFix_choose cCCexp \<Gamma> \<cdot> (cCCexp e\<cdot>n))"
  "cCCexp (Bool b)\<cdot>n = \<bottom>"
  "cCCexp (scrut ? e1 : e2)\<cdot>n = (fst (cCCexp scrut\<cdot>0) \<squnion> fst (cCCexp e1\<cdot>n) \<squnion> fst (cCCexp e2\<cdot>n),
        snd (cCCexp scrut\<cdot>0) \<squnion> (snd (cCCexp e1\<cdot>n) \<squnion> snd (cCCexp e2\<cdot>n)) \<squnion> ccProd (edom (fst (cCCexp scrut\<cdot>0))) (edom (fst (cCCexp e1\<cdot>n)) \<union> edom (fst (cCCexp e2\<cdot>n))))"
by (simp_all)
declare cCCexp.simps[simp del]


lemma Aexp_simps[simp]:
  "Aexp (Var x)\<cdot>n = esing x\<cdot>(up\<cdot>n)"
  "Aexp (Lam [x]. e)\<cdot>n = Aexp e\<cdot>(pred\<cdot>n) f|` fv (Lam [x]. e)"
  "Aexp (App e x)\<cdot>n = Aexp e\<cdot>(inc\<cdot>n) \<squnion> esing x\<cdot>(up\<cdot>0)"
  "\<not> nonrec \<Gamma> \<Longrightarrow> Aexp (Let \<Gamma> e)\<cdot>n = (Afix \<Gamma>\<cdot>(Aexp e\<cdot>n \<squnion> (\<lambda>_.up\<cdot>0) f|` thunks \<Gamma>)) f|` (fv (Let \<Gamma> e))"
  "x \<notin> fv e \<Longrightarrow> Aexp (let x be e in exp)\<cdot>n = (fup\<cdot>(Aexp e)\<cdot>(ABind_nonrec x e \<cdot> (Aexp exp\<cdot>n, CCexp exp\<cdot>n)) \<squnion> Aexp exp\<cdot>n) f|` (fv (let x be e in exp))"
  "Aexp (Bool b)\<cdot>n = \<bottom>"
  "Aexp (scrut ? e1 : e2)\<cdot>n = Aexp scrut\<cdot>0 \<squnion> Aexp e1\<cdot>n \<squnion> Aexp e2\<cdot>n"
 by (simp add: cccFix_eq Aexp_eq fup_Aexp_eq CCexp_eq fup_CCexp_eq)+


lemma CCexp_simps[simp]:
  "CCexp (Var x)\<cdot>n = \<bottom>"
  "CCexp (Lam [x]. e)\<cdot>n = predCC (fv (Lam [x]. e)) (CCexp e)\<cdot>n"
  "CCexp (App e x)\<cdot>n = CCexp e\<cdot>(inc\<cdot>n) \<squnion> ccProd {x} (insert x (fv e))"
  "\<not> nonrec \<Gamma> \<Longrightarrow> CCexp (Let \<Gamma> e)\<cdot>n = cc_restr (fv (Let \<Gamma> e)) (CCfix \<Gamma>\<cdot>(Afix \<Gamma>\<cdot>(Aexp e\<cdot>n  \<squnion> (\<lambda>_.up\<cdot>0) f|` (thunks \<Gamma>)), CCexp e\<cdot>n))"
  "x \<notin> fv e \<Longrightarrow> CCexp (let x be e in exp)\<cdot>n =
    cc_restr (fv (let x be e in exp)) (ccBind x e \<cdot>(Aheap_nonrec x e\<cdot>(Aexp exp\<cdot>n, CCexp exp\<cdot>n), CCexp exp\<cdot>n) \<squnion> ccProd (fv e) (ccNeighbors x (CCexp exp\<cdot>n) - (if isVal e then {} else {x})) \<squnion> CCexp exp\<cdot>n)"
  "CCexp (Bool b)\<cdot>n = \<bottom>"
  "CCexp (scrut ? e1 : e2)\<cdot>n = CCexp scrut\<cdot>0 \<squnion> (CCexp e1\<cdot>n \<squnion> CCexp e2\<cdot>n) \<squnion> ccProd (edom (Aexp scrut\<cdot>0)) (edom (Aexp e1\<cdot>n) \<union> edom (Aexp e2\<cdot>n))"
by (simp add: cccFix_eq Aexp_eq fup_Aexp_eq CCexp_eq fup_CCexp_eq predCC_eq)+

lemma 
  shows ccField_CCexp: "ccField (CCexp e\<cdot>n) \<subseteq> fv e" and Aexp_edom': "edom (Aexp e\<cdot>n) \<subseteq> fv e"
  apply (induction e arbitrary: n rule: exp_induct_rec)
  apply (auto simp add: predCC_eq dest!: set_mp[OF ccField_cc_restr] set_mp[OF ccField_ccProd_subset])
  apply fastforce+
  done

lemma cc_restr_CCexp[simp]:
  "cc_restr (fv e) (CCexp e\<cdot>a) = CCexp e\<cdot>a"
by (rule cc_restr_noop[OF ccField_CCexp])

lemma ccField_fup_CCexp:
  "ccField (fup\<cdot>(CCexp e)\<cdot>n) \<subseteq> fv e"
by (cases n) (auto dest: set_mp[OF ccField_CCexp])

lemma cc_restr_fup_ccExp_useless[simp]: "cc_restr (fv e) (fup\<cdot>(CCexp e)\<cdot>n) = fup\<cdot>(CCexp e)\<cdot>n"
  by (rule cc_restr_noop[OF ccField_fup_CCexp])


sublocale EdomArityAnalysis Aexp by standard (rule Aexp_edom')



definition Aheap where
  "Aheap \<Gamma> e = (\<Lambda> a. if nonrec \<Gamma> then (case_prod Aheap_nonrec (hd \<Gamma>))\<cdot>(Aexp e\<cdot>a, CCexp e\<cdot>a) else  (Afix \<Gamma> \<cdot> (Aexp e\<cdot>a \<squnion> (\<lambda>_.up\<cdot>0) f|` thunks \<Gamma>)) f|` domA \<Gamma>)"

lemma Aheap_simp1[simp]:
  "\<not> nonrec \<Gamma> \<Longrightarrow> Aheap \<Gamma> e \<cdot>a = (Afix \<Gamma> \<cdot> (Aexp e\<cdot>a \<squnion> (\<lambda>_.up\<cdot>0) f|` thunks \<Gamma>)) f|` domA \<Gamma>"
  unfolding Aheap_def by simp

lemma Aheap_simp2[simp]:
  "x \<notin> fv e' \<Longrightarrow> Aheap [(x,e')] e \<cdot>a = Aheap_nonrec x e'\<cdot>(Aexp e\<cdot>a, CCexp e\<cdot>a)"
  unfolding Aheap_def by (simp add: nonrec_def)

lemma Aheap_eqvt'[eqvt]:
  "\<pi> \<bullet> (Aheap \<Gamma> e) = Aheap (\<pi> \<bullet> \<Gamma>) (\<pi> \<bullet> e)"
  apply (rule cfun_eqvtI)
  apply (cases nonrec \<pi> rule: eqvt_cases[where x = \<Gamma>])
  apply simp
  apply (erule nonrecE)
  apply simp
  apply (erule nonrecE)
  apply simp
  apply (perm_simp, rule)
  apply simp
  apply (perm_simp, rule)
  done

sublocale ArityAnalysisHeap Aheap.

sublocale ArityAnalysisHeapEqvt Aheap
proof
  fix \<pi> show "\<pi> \<bullet> Aheap = Aheap"
    by perm_simp rule
qed

lemma Aexp_lam_simp[simp]: "Aexp (Lam [x]. e) \<cdot> n = env_delete x (Aexp e \<cdot> (pred \<cdot> n))"
proof-
  have "Aexp (Lam [x]. e) \<cdot> n = Aexp e\<cdot>(pred\<cdot>n) f|` (fv e - {x})" by simp
  also have "... = env_delete x (Aexp e\<cdot>(pred\<cdot>n)) f|` (fv e - {x})" by simp
  also have "\<dots> = env_delete x (Aexp e\<cdot>(pred\<cdot>n))"
     by (rule env_restr_useless) (auto dest: set_mp[OF Aexp_edom])
  finally show ?thesis.
qed
declare Aexp_simps(2)[simp del]

lemma Aexp_Let_simp1[simp]:
  "\<not> nonrec \<Gamma> \<Longrightarrow> Aexp (Let \<Gamma> e)\<cdot>n = (Afix \<Gamma>\<cdot>(Aexp e\<cdot>n \<squnion> (\<lambda>_.up\<cdot>0) f|` thunks \<Gamma>)) f|` (- domA \<Gamma>)"
  unfolding Aexp_simps
  by (rule env_restr_cong) (auto dest!: set_mp[OF Afix_edom] set_mp[OF Aexp_edom] set_mp[OF thunks_domA])

lemma Aexp_Let_simp2[simp]:
  "x \<notin> fv e \<Longrightarrow> Aexp (let x be e in exp)\<cdot>n = env_delete x (fup\<cdot>(Aexp e)\<cdot>(ABind_nonrec x e \<cdot> (Aexp exp\<cdot>n, CCexp exp\<cdot>n)) \<squnion> Aexp exp\<cdot>n)"
  unfolding Aexp_simps env_delete_restr
  by (rule env_restr_cong) (auto dest!: set_mp[OF fup_Aexp_edom]  set_mp[OF Aexp_edom])

declare Aexp_simps(4)[simp del]
declare Aexp_simps(5)[simp del]

end


end

