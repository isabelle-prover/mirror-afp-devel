(*  Title:      JinjaThreads/Compiler/JVMJ1.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Correctness of Stage 2: From JVM to intermediate language} *}

theory JVMJ1 imports J1JVMBisim begin

lemma assumes ha: "h a = \<lfloor>Obj D fs\<rfloor>"
  and subclsObj: "P \<turnstile> D \<preceq>\<^sup>* Throwable"
  shows bisim1_xcp_\<tau>Red:
  "\<lbrakk> P,e,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>);
    match_ex_table (compP f P) (cname_of h a) pc (compxE2 e 0 0) = None;
    n + max_vars e' \<le> length xs \<rbrakk>
  \<Longrightarrow> \<tau>Red P h e' xs (Throw a) loc \<and> P,e,n,h \<turnstile> (Throw a, loc) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"

  and bisims1_xcp_\<tau>Reds:
  "\<lbrakk> P,es,n,h \<turnstile> (es', xs) [\<leftrightarrow>] (stk, loc, pc, \<lfloor>a\<rfloor>);
     match_ex_table (compP f P) (cname_of h a) pc (compxEs2 es 0 0) = None;
     n + max_varss es' \<le> length xs \<rbrakk>
  \<Longrightarrow> \<exists>vs es''. \<tau>Reds P h es' xs (map Val vs @ Throw a # es'') loc \<and>
               P,es,n,h \<turnstile> (map Val vs @ Throw a # es'', loc) [\<leftrightarrow>] (stk, loc, pc, \<lfloor>a\<rfloor>)"
proof(induct e n e' xs stk loc pc xcp\<equiv>"\<lfloor>a::addr\<rfloor>" and es n es' xs stk loc pc xcp\<equiv>"\<lfloor>a::addr\<rfloor>"
      rule: bisim1_bisims1.inducts[split_format (complete)])
  case (bisim1TryFail e V a' xs stk loc pc C'' fs C' e2)
  note bisim = `P,e,V,h \<turnstile> (Throw a', xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a'\<rfloor>)`
  hence "xs = loc" by(auto dest: bisim1_ThrowD)
  with bisim `h a' = \<lfloor>Obj C'' fs\<rfloor>` `\<lfloor>a'\<rfloor> = \<lfloor>a\<rfloor>` `\<not> P \<turnstile> C'' \<preceq>\<^sup>* C'` `bsok e2 (Suc V)`
  show ?case by(auto intro: \<tau>Red_refl bisim1_bisims1.bisim1TryFail)
next
  case (bisim1Try e V e' xs stk loc pc xcp e2 C)
  hence red: "\<tau>Red P h e' xs (Throw a) loc"
    and bisim: "P,e,V,h \<turnstile> (Throw a, loc) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"
    by(auto simp add: match_ex_table_append)
  from red have Red: "\<tau>Red P h (try e' catch(C V) e2) xs (try Throw a catch(C V) e2) loc" by auto
  from `match_ex_table (compP f P) (cname_of h a) pc (compxE2 (try e catch(C V) e2) 0 0) = None`
  have "\<not> matches_ex_entry (compP f P) (cname_of h a) pc (0, length (compE2 e), C, Suc (length (compE2 e)), 0)"
    by(auto simp add: match_ex_table_append split: split_if_asm)
  moreover from `P,e,V,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)` `xcp = \<lfloor>a\<rfloor>`
  have "pc < length (compE2 e)" by(auto dest: bisim1_xcp_pcD)
  ultimately have subcls: "\<not> P \<turnstile> D \<preceq>\<^sup>* C" using ha by(simp add: matches_ex_entry_def)
  with ha have "P \<turnstile>1 \<langle>try Throw a catch(C V) e2, (h, loc)\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a, (h, loc)\<rangle>"
    by -(rule Red1TryFail, auto)
  moreover from bisim ha subcls `bsok e2 (Suc V)`
  have "P,try e catch(C V) e2,V,h \<turnstile> (Throw a, loc) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"
    by(rule bisim1TryFail)
  ultimately show ?case using Red by(blast intro: \<tau>Red_step \<tau>move1TryFail)
next
  case (bisim1TryCatch2 e2 V e' xs stk loc pc xcp e1 C)
  hence "\<tau>Red P h e' xs (Throw a) loc \<and> P,e2,Suc V,h \<turnstile> (Throw a, loc) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"
    by(clarsimp simp add: match_ex_table_append matches_ex_entry_def split: split_if_asm)(clarsimp simp add: match_ex_table_append compxE2_size_convs compxE2_stack_xlift_convs match_ex_table_shift_pc_None)
  moreover note \<tau>Red_preserves_len[OF this[THEN conjunct1]]
  moreover from `V + max_vars {V:Class C=None; e'}\<^bsub>False\<^esub> \<le> length xs` have "V < length xs" by simp
  ultimately show ?case using `bsok e1 V`
    by(fastsimp intro: \<tau>Red_step Block1ThrowNone \<tau>move1BlockThrow bisim1TryCatchThrow)
next
  case (bisim1TryCatchThrow e2 V a' xs stk loc pc e C')
  from `\<lfloor>a'\<rfloor> = \<lfloor>a\<rfloor>` have [simp]: "a = a'" by simp
  from `P,e2,Suc V,h \<turnstile> (Throw a', xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a'\<rfloor>)` have "xs = loc"
    by(auto dest: bisim1_ThrowD)
  with `P,e2,Suc V,h \<turnstile> (Throw a', xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a'\<rfloor>)` `bsok e V` show ?case
    by(auto intro: \<tau>Red_refl bisim1_bisims1.bisim1TryCatchThrow)
next
  case bisims1Nil thus ?case
    by(clarsimp simp add: match_ex_table_append compxE2_size_convs compxE2_stack_xlift_convs match_ex_table_shift_pc_None)
next
  case (bisims1List1 e n e' xs stk loc pc xcp es)
  hence "\<tau>Red P h e' xs (Throw a) loc"
    and bisim: "P,e,n,h \<turnstile> (Throw a, loc) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)" by(auto simp add: match_ex_table_append)
  hence "\<tau>Reds P h (e' # es) xs (map Val [] @ Throw a # es) loc" by(auto intro: \<tau>Red_inj_\<tau>Reds)
  moreover from bisim `bsoks es n` 
  have "P,e#es,n,h \<turnstile> (Throw a # es, loc) [\<leftrightarrow>] (stk, loc, pc, \<lfloor>a\<rfloor>)"
    by(rule bisim1_bisims1.bisims1List1)
  ultimately show ?case by fastsimp
next
  case (bisims1List2 es n es' xs stk loc pc xcp e v)
  hence "\<exists>vs es''. \<tau>Reds P h es' xs (map Val vs @ Throw a # es'') loc \<and> P,es,n,h \<turnstile> (map Val vs @ Throw a # es'', loc) [\<leftrightarrow>] (stk, loc, pc, \<lfloor>a\<rfloor>)"
    by(clarsimp simp add: match_ex_table_append_not_pcs compxEs2_size_convs compxEs2_stack_xlift_convs match_ex_table_shift_pc_None)
  then obtain vs es'' where red: "\<tau>Reds P h es' xs (map Val vs @ Throw a # es'') loc" 
    and bisim: "P,es,n,h \<turnstile> (map Val vs @ Throw a # es'', loc) [\<leftrightarrow>] (stk, loc, pc, \<lfloor>a\<rfloor>)" by blast
  from red have "\<tau>Reds P h (Val v # es') xs (map Val (v # vs) @ Throw a # es'') loc"
    by(auto intro: \<tau>Reds_cons_\<tau>Reds)
  moreover from bisim `bsok e n`
  have "P,e # es,n,h \<turnstile> (map Val (v # vs) @ Throw a # es'', loc) [\<leftrightarrow>] (stk @ [v], loc, length (compE2 e) + pc, \<lfloor>a\<rfloor>)"
    by(auto intro: bisim1_bisims1.bisims1List2)
  ultimately show ?case by fastsimp
next
  case (bisim1WhileThrow2 e n a' xs stk loc pc c)
  note bisim = `P,e,n,h \<turnstile> (Throw a', xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a'\<rfloor>)`
  hence "xs = loc" by(auto dest: bisim1_ThrowD)
  with `\<lfloor>a'\<rfloor> = \<lfloor>a\<rfloor>` bisim `bsok c n` show ?case
    by(auto intro: \<tau>Red_refl bisim1_bisims1.bisim1WhileThrow2)
next
  case bisim1Seq2 thus ?case
    by(clarsimp simp add: match_ex_table_append_not_pcs compxE2_size_convs compxE2_stack_xlift_convs match_ex_table_shift_pc_None)(rule bisim1_bisims1.bisim1Seq2)
next
  case bisim1CondThen thus ?case
    by(clarsimp simp add: match_ex_table_append)
     (clarsimp simp add: match_ex_table_append_not_pcs compxE2_size_convs compxE2_stack_xlift_convs match_ex_table_shift_pc_None, rule bisim1_bisims1.bisim1CondThen) 
next
  case bisim1CondElse thus ?case
    by(clarsimp simp add: match_ex_table_append)
      (clarsimp simp add: match_ex_table_append_not_pcs compxE2_size_convs compxE2_stack_xlift_convs match_ex_table_shift_pc_None, rule bisim1_bisims1.bisim1CondElse)
next
  case (bisim1While4 e n e' xs stk loc pc xcp c)
  hence "\<tau>Red P h e' xs (Throw a) loc \<and> P,e,n,h \<turnstile> (Throw a, loc) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"
    by(clarsimp simp add: match_ex_table_append_not_pcs compxE2_size_convs compxEs2_size_convs compxE2_stack_xlift_convs compxEs2_stack_xlift_convs match_ex_table_shift_pc_None)
  with `bsok c n` have "\<tau>Red P h (e';;while (c) e) xs (Throw a) loc"
    "P,while (c) e,n,h \<turnstile> (Throw a, loc) \<leftrightarrow> (stk, loc, Suc (length (compE2 c) + pc), \<lfloor>a\<rfloor>)"
    by(auto intro: \<tau>Red_step Seq1Throw \<tau>move1SeqThrow bisim1WhileThrow2)
  thus ?case ..
next
  case bisim1BinOp2 thus ?case
    by(clarsimp simp add: match_ex_table_append_not_pcs compxE2_size_convs compxE2_stack_xlift_convs match_ex_table_shift_pc_None)
      (auto intro: \<tau>Red_step red1_reds1.intros \<tau>move1_\<tau>moves1.intros bisim1BinOpThrow2)
next
  case (bisim1BinOpThrow2 e n a' xs stk loc pc e1 bop)
  note bisim = `P,e,n,h \<turnstile> (Throw a', xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a'\<rfloor>)`
  hence "xs = loc" by(auto dest: bisim1_ThrowD)
  with `\<lfloor>a'\<rfloor> = \<lfloor>a\<rfloor>` bisim `bsok e1 n` show ?case
    by(auto intro: \<tau>Red_refl bisim1_bisims1.bisim1BinOpThrow2)
next
  case bisim1CallParams thus ?case
    by(clarsimp simp add: match_ex_table_append_not_pcs compxE2_size_convs compxEs2_size_convs compxE2_stack_xlift_convs compxEs2_stack_xlift_convs match_ex_table_shift_pc_None)
      (auto intro: \<tau>Red_step red1_reds1.intros \<tau>move1_\<tau>moves1.intros bisim1CallThrowParams)
next
  case (bisim1CallThrowParams es n vs a' es' xs stk loc pc obj M)
  note bisim = `P,es,n,h \<turnstile> (map Val vs @ Throw a' # es', xs) [\<leftrightarrow>] (stk, loc, pc, \<lfloor>a'\<rfloor>)`
  hence "xs = loc" by(auto dest: bisims1_ThrowD)
  with `\<lfloor>a'\<rfloor> = \<lfloor>a\<rfloor>` bisim `bsok obj n` show ?case
    by(auto intro: \<tau>Red_refl bisim1_bisims1.bisim1CallThrowParams)
next
  case (bisim1BlockSome3 e V e' xs v stk loc pc xcp Ty)
  from `V + max_vars {V:Ty=\<lfloor>v\<rfloor>; e'}\<^bsub>False\<^esub> \<le> length xs` have V: "V < length xs" by simp
  from bisim1BlockSome3 have red: "\<tau>Red P h e' (xs[V := v]) (Throw a) loc"
    and bisim: "P,e,Suc V,h \<turnstile> (Throw a, loc) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"
    by(clarsimp simp add: match_ex_table_append_not_pcs compxE2_size_convs compxEs2_size_convs compxE2_stack_xlift_convs compxEs2_stack_xlift_convs match_ex_table_shift_pc_None)+
  from red show ?case
  proof(cases rule: converse_\<tau>RedE)
    assume "e' = Throw a" "xs[V := v] = loc"
    moreover from V have "P \<turnstile>1 \<langle>{V:Ty=\<lfloor>v\<rfloor>; Throw a}\<^bsub>False\<^esub>,(h, xs)\<rangle> -\<epsilon>\<rightarrow> \<langle>Throw a,(h, xs[V := v])\<rangle>"
      by(rule Block1ThrowSome)
    moreover have "\<tau>move1 {V:Ty=\<lfloor>v\<rfloor>; Throw a}\<^bsub>False\<^esub>" by(rule \<tau>move1BlockThrow)
    ultimately show ?thesis using bisim by(auto intro: \<tau>Red1step bisim1BlockThrowSome)
  next
    fix e'' xs''
    assume red: "P \<turnstile>1 \<langle>e',(h, xs[V := v])\<rangle> -\<epsilon>\<rightarrow> \<langle>e'',(h, xs'')\<rangle>"
      and \<tau>: "\<tau>move1 e'"
      and Red: "\<tau>Red P h e'' xs'' (Throw a) loc"
    from red V have "P \<turnstile>1 \<langle>{V:Ty=\<lfloor>v\<rfloor>; e'}\<^bsub>False\<^esub>, (h, xs)\<rangle> -\<epsilon>\<rightarrow> \<langle>{V:Ty=None; e''}\<^bsub>False\<^esub>,(h, xs'')\<rangle>"
      by(rule Block1RedSome)
    moreover from \<tau> have "\<tau>move1 {V:Ty=\<lfloor>v\<rfloor>; e'}\<^bsub>False\<^esub>" by(rule \<tau>move1Block)
    moreover from red Red have len: "length loc = length xs''" "length xs'' = length xs"
      by(auto dest: red1_preserves_len \<tau>Red_preserves_len)
    with Red V have "\<tau>Red P h {V:Ty=None; e''}\<^bsub>False\<^esub> xs'' {V:Ty=None; Throw a}\<^bsub>False\<^esub> loc" by auto
    hence "\<tau>Red P h {V:Ty=None; e''}\<^bsub>False\<^esub> xs'' (Throw a) loc" using V len
      by(auto intro: \<tau>move1BlockThrow Block1ThrowNone elim!: \<tau>Red_step)
    ultimately show ?thesis using bisim by(auto intro: converse_\<tau>Red_step bisim1BlockThrowSome)
  qed
next
  case (bisim1BlockSome4 e V e' xs stk loc pc xcp Ty v)
  from `V + max_vars {V:Ty=None; e'}\<^bsub>False\<^esub> \<le> length xs` have V: "V < length xs" by simp
  from bisim1BlockSome4 have Red: "\<tau>Red P h e' xs (Throw a) loc"
    and bisim: "P,e,Suc V,h \<turnstile> (Throw a, loc) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)"
    by(clarsimp simp add: match_ex_table_append_not_pcs compxE2_size_convs compxEs2_size_convs compxE2_stack_xlift_convs compxEs2_stack_xlift_convs match_ex_table_shift_pc_None)+
  note len = \<tau>Red_preserves_len[OF Red]
  with Red V have "\<tau>Red P h {V:Ty=None; e'}\<^bsub>False\<^esub> xs {V:Ty=None; Throw a}\<^bsub>False\<^esub> loc" by auto
  thus ?case using V len bisim 
    by(auto intro: \<tau>move1BlockThrow Block1ThrowNone bisim1BlockThrowSome elim!: \<tau>Red_step)    
next
  case bisim1BlockThrowSome thus ?case
    by(auto dest: bisim1_ThrowD intro: \<tau>Red_refl bisim1_bisims1.bisim1BlockThrowSome)
next
  case (bisim1BlockNone e V e' xs stk loc pc xcp Ty)
  hence Red: "\<tau>Red P h e' xs (Throw a) loc" and bisim: "P,e,Suc V,h \<turnstile> (Throw a, loc) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)" by auto
  from Red have len: "length loc = length xs" by(rule \<tau>Red_preserves_len)
  from `V + max_vars {V:Ty=None; e'}\<^bsub>False\<^esub> \<le> length xs` have V: "V < length xs" by simp
  from Red len V have "\<tau>Red P h {V:Ty=None; e'}\<^bsub>False\<^esub> xs {V:Ty=None; Throw a}\<^bsub>False\<^esub> loc" by auto
  thus ?case using V len bisim by(auto intro: \<tau>move1BlockThrow Block1ThrowNone bisim1BlockThrowNone elim!: \<tau>Red_step)
next
  case bisim1BlockThrowNone thus ?case
    by(auto dest: bisim1_ThrowD intro: \<tau>Red_refl bisim1_bisims1.bisim1BlockThrowNone)
next
  case (bisim1Sync4 e2 V e' xs stk loc pc xcp e1 a')
  from `xcp = \<lfloor>a\<rfloor>` `P,e2,Suc V,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  have "pc < length (compE2 e2)" by(auto dest!: bisim1_xcp_pcD)
  with `match_ex_table (compP f P) (cname_of h a) (Suc (Suc (Suc (length (compE2 e1) + pc)))) (compxE2 (sync\<^bsub>V\<^esub> (e1) e2) 0 0) = None` subclsObj ha
  have False by(simp add: match_ex_table_append matches_ex_entry_def split: split_if_asm)
  thus ?case ..
next
  case bisim1AAcc2 thus ?case
    by(clarsimp simp add: match_ex_table_append_not_pcs compxE2_size_convs compxE2_stack_xlift_convs match_ex_table_shift_pc_None)
      (auto intro: \<tau>Red_step red1_reds1.intros \<tau>move1_\<tau>moves1.intros bisim1AAccThrow2)
next
  case (bisim1AAccThrow2 e n a' xs stk loc pc i)
  note bisim = `P,e,n,h \<turnstile> (Throw a', xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a'\<rfloor>)`
  hence "xs = loc" by(auto dest: bisim1_ThrowD)
  with `\<lfloor>a'\<rfloor> = \<lfloor>a\<rfloor>` bisim `bsok i n` show ?case
    by(auto intro: \<tau>Red_refl bisim1_bisims1.bisim1AAccThrow2)
next
  case bisim1AAss2 thus ?case
    by(clarsimp simp add: compxE2_size_convs compxE2_stack_xlift_convs)
      (auto simp add: match_ex_table_append intro: \<tau>Red_step red1_reds1.intros \<tau>move1_\<tau>moves1.intros bisim1AAssThrow2)
next
  case bisim1AAss3 thus ?case
    by(clarsimp simp add: compxE2_size_convs compxE2_stack_xlift_convs)
      (auto simp add: match_ex_table_append intro: \<tau>Red_step red1_reds1.intros \<tau>move1_\<tau>moves1.intros bisim1AAssThrow3)
next
  case (bisim1AAssThrow2 e n a' xs stk loc pc i e2)
  note bisim = `P,e,n,h \<turnstile> (Throw a', xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a'\<rfloor>)`
  hence "xs = loc" by(auto dest: bisim1_ThrowD)
  with `\<lfloor>a'\<rfloor> = \<lfloor>a\<rfloor>` bisim `bsok i n` `bsok e2 n` show ?case
    by(auto intro: \<tau>Red_refl bisim1_bisims1.bisim1AAssThrow2)
next
  case (bisim1AAssThrow3 e n a' xs stk loc pc A i)
  note bisim = `P,e,n,h \<turnstile> (Throw a', xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a'\<rfloor>)`
  hence "xs = loc" by(auto dest: bisim1_ThrowD)
  with `\<lfloor>a'\<rfloor> = \<lfloor>a\<rfloor>` bisim `bsok i n` `bsok A n` show ?case
    by(auto intro: \<tau>Red_refl bisim1_bisims1.bisim1AAssThrow3)
next
  case bisim1FAss2 thus ?case
    by(clarsimp simp add: match_ex_table_append_not_pcs compxE2_size_convs compxE2_stack_xlift_convs)
      (auto intro: \<tau>Red_step red1_reds1.intros \<tau>move1_\<tau>moves1.intros bisim1FAssThrow2)
next
  case (bisim1FAssThrow2 e2 n a' xs stk loc pc e)
  note bisim = `P,e2,n,h \<turnstile> (Throw a', xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a'\<rfloor>)`
  hence "xs = loc" by(auto dest: bisim1_ThrowD)
  with `\<lfloor>a'\<rfloor> = \<lfloor>a\<rfloor>` bisim `bsok e n` show ?case
    by(auto intro: \<tau>Red_refl bisim1_bisims1.bisim1FAssThrow2)
qed(fastsimp intro: \<tau>Red_step \<tau>Red_refl red1_reds1.intros \<tau>move1_\<tau>moves1.intros bisim1_bisims1.intros simp add: match_ex_table_append dest: bisim1_ThrowD)+

lemma shows bisim1_WTrt1_Throw_ObjD:
  "\<lbrakk> P,e,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>); P,Env,h \<turnstile>1 e' : T \<rbrakk> \<Longrightarrow> \<exists>C. typeof\<^bsub>h\<^esub> (Addr a) = \<lfloor>Class C\<rfloor> \<and> P \<turnstile> C \<preceq>\<^sup>* Throwable"

  and bisims1_WTrts1_Throw_ObjD: 
  "\<lbrakk> P,es,n,h \<turnstile> (es', xs) [\<leftrightarrow>] (stk, loc, pc, \<lfloor>a\<rfloor>); P,Env,h \<turnstile>1 es' [:] Ts \<rbrakk> \<Longrightarrow> \<exists>C. typeof\<^bsub>h\<^esub> (Addr a) = \<lfloor>Class C\<rfloor> \<and> P \<turnstile> C \<preceq>\<^sup>* Throwable"
apply(induct e n e' xs stk loc pc xcp\<equiv>"\<lfloor>a::addr\<rfloor>" and es n es' xs stk loc pc xcp\<equiv>"\<lfloor>a::addr\<rfloor>"
      arbitrary: Env T and Env Ts rule: bisim1_bisims1_inducts_split)
apply(fastsimp split: heapobj.split_asm dest: Array_widen)+
done

lemma assumes wf: "wf_J1_prog P"
  and hconf: "P \<turnstile> h \<surd>"
  shows red1_simulates_exec_instr:
  "\<lbrakk> P, E, n, h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, xcp);
     exec_move P E h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp');
     n + max_vars e \<le> length xs;
     P,Env,h \<turnstile>1 e : T \<rbrakk>
  \<Longrightarrow> \<exists>e'' xs''. P, E, n, h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp') \<and>
     (if \<tau>move2 E pc xcp
      then h' = h \<and> \<tau>Red P h e xs e'' xs''
      else \<exists>ta' e' xs'. \<tau>Red P h e xs e' xs' \<and> P \<turnstile>1 \<langle>e', (h, xs')\<rangle> -ta'\<rightarrow> \<langle>e'', (h', xs'')\<rangle> \<and> ta_bisim (wbisim1 P) ta' ta \<and> \<not> \<tau>move1 e')"
  (is "\<lbrakk> _; ?exec E stk loc pc xcp stk' loc' pc' xcp'; _; _ \<rbrakk>
       \<Longrightarrow> \<exists>e'' xs''. P, E, n, h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp') \<and> ?red e xs e'' xs'' E pc xcp")

  and reds1_simulates_exec_instr:
  "\<lbrakk> P, Es, n, h \<turnstile> (es, xs) [\<leftrightarrow>] (stk, loc, pc, xcp);
     exec_moves P Es h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp');
     n + max_varss es \<le> length xs;
     P,Env,h \<turnstile>1 es [:] Ts \<rbrakk>
  \<Longrightarrow> \<exists>es'' xs''. P, Es, n, h' \<turnstile> (es'', xs'') [\<leftrightarrow>] (stk', loc', pc', xcp') \<and>
     (if \<tau>moves2 Es pc xcp
      then h' = h \<and> \<tau>Reds P h es xs es'' xs''
      else \<exists>ta' es' xs'. \<tau>Reds P h es xs es' xs' \<and> P \<turnstile>1 \<langle>es', (h, xs')\<rangle> [-ta'\<rightarrow>] \<langle>es'', (h', xs'')\<rangle> \<and> ta_bisim (wbisim1 P) ta' ta \<and> \<not> \<tau>moves1 es')"
  (is "\<lbrakk> _; ?execs Es stk loc pc xcp stk' loc' pc' xcp'; _; _ \<rbrakk>
       \<Longrightarrow> \<exists>es'' xs''. P, Es, n, h' \<turnstile> (es'', xs'') [\<leftrightarrow>] (stk', loc', pc', xcp') \<and> ?reds es xs es'' xs'' Es pc xcp")
proof(induct arbitrary: stk' loc' pc' xcp' Env T and stk' loc' pc' xcp' Env Ts rule: bisim1_bisims1_inducts_split)
  case (bisim1BlockSome3 e V e' xs v stk loc pc xcp Ty)
  note bisim = `P,e,Suc V,h \<turnstile> (e', xs[V := v]) \<leftrightarrow> (stk, loc, pc, xcp)`
  note IH1 = `\<And>stk' loc' pc' xcp' Env T. 
             \<lbrakk> ?exec e stk loc pc xcp stk' loc' pc' xcp'; Suc V + max_vars e' \<le> length (xs[V := v]); P,Env,h \<turnstile>1 e' : T \<rbrakk>
             \<Longrightarrow> \<exists>e'' xs''. P, e, Suc V, h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp') \<and> ?red e' (xs[V := v]) e'' xs'' e pc xcp`
  note exec = `exec_move P {V:Ty=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub> h (stk, loc, Suc (Suc pc), xcp) ta h' (stk', loc', pc', xcp')`
  from `P,Env,h \<turnstile>1 {V:Ty=\<lfloor>v\<rfloor>; e'}\<^bsub>False\<^esub> : T` have wte: "P,Env@[Ty],h \<turnstile>1 e' : T" by auto
  from `V + max_vars {V:Ty=\<lfloor>v\<rfloor>; e'}\<^bsub>False\<^esub> \<le> length xs`
  have len: "Suc V + max_vars e' \<le> length xs" and V: "V < length xs" by simp_all
  let ?pre = "[Push v, Store V]"

  from exec have exec': "exec_meth (compP2 P) (?pre @ compE2 e) (shift (length ?pre) (compxE2 e 0 0)) h (stk, loc, length ?pre + pc, xcp) ta h' (stk', loc', pc', xcp')" by(simp add: compxE2_size_convs exec_move_def)
  hence "exec_meth (compP2 P) (compE2 e) (compxE2 e 0 0) h (stk, loc, pc, xcp) ta h' (stk', loc', pc' - length ?pre, xcp')"
    by(rule exec_meth_drop)auto
  from IH1[OF this[folded exec_move_def] _ wte] len obtain e'' xs''
    where bisim': "P,e,Suc V,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc' - length ?pre, xcp')"
    and red: "?red e' (xs[V := v]) e'' xs'' e pc xcp" by auto
  from exec' have pc': "pc' \<ge> length ?pre" by(rule exec_meth_drop_pc)(auto)
  hence pc'': "Suc (Suc (pc' - Suc (Suc 0))) = pc'" by simp
  show ?case
  proof(cases "\<tau>move2 e pc xcp")
    case True
    note \<tau> = True
    hence \<tau>': "\<tau>move2 {V:Ty=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub> (Suc (Suc pc)) xcp" by(rule \<tau>move2BlockSome)
    show ?thesis using red \<tau> bisim' pc'' V
      apply clarsimp
      apply(erule converse_\<tau>RedE)
       apply(clarsimp)
       apply(rule exI conjI impI)+
         apply(subst pc''[symmetric])
	 apply(erule bisim1_bisims1.bisim1BlockSome3)
	apply(rule \<tau>Red_refl)
       apply(clarsimp)
       apply(erule notE)
       apply(erule \<tau>move2BlockSome)
      apply(rule exI conjI impI)+
        apply(subst pc''[symmetric])
	apply(erule bisim1_bisims1.bisim1BlockSome4)
       apply(rule converse_\<tau>Red_step)
         apply(erule (1) Block1RedSome)
	apply(erule \<tau>move1Block)
       apply(rule Block_\<tau>Red_None, assumption)
       apply(drule \<tau>Red_preserves_len)
       apply(drule red1_preserves_len)
       apply simp
      apply clarsimp
      apply(erule notE)
      apply(erule \<tau>move2BlockSome)
      done
  next
    case False
    hence \<tau>': "\<not> \<tau>move2 {V:Ty=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub> (Suc (Suc pc)) xcp" by auto
    from bisim' have bisim'': "P,{V:Ty=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub>,V,h' \<turnstile> ({V:Ty=None; e''}\<^bsub>False\<^esub>, xs'') \<leftrightarrow> (stk', loc', Suc (Suc (pc' - Suc (Suc 0))), xcp')"
      by -(rule bisim1BlockSome4, simp)
    with False red bisim' \<tau>' pc'' V show ?thesis
      apply clarsimp
      apply(rule exI conjI)+
      apply assumption
      apply(erule converse_\<tau>RedE)
       apply(clarsimp)
       apply(rule exI conjI)+
        apply(rule \<tau>Red_refl)
       apply(rule conjI)
	apply(erule (1) Block1RedSome)
       apply(fastsimp)
      apply(rule exI conjI)+
       apply(rule converse_\<tau>Red_step)
         apply(erule (1) Block1RedSome)
        apply(erule \<tau>move1Block)
       apply(erule Block_None_\<tau>Red_xt)
      apply(drule red1_preserves_len)+
      apply simp
     apply(rule conjI)
      apply(erule Block1RedNone)
      apply(drule \<tau>Red_preserves_len)
      apply simp
     apply(auto)
     apply(drule red1_preserves_len)
     apply simp
     done
 qed
next
  case (bisim1Val2 e n v xs)
  from `?exec e [v] xs (length (compE2 e)) None stk' loc' pc' xcp'`
  have False by(auto dest: exec_meth_length_compE2D simp add: exec_move_def)
  thus ?case ..
next
  case (bisim1New C' n xs)
  note exec = `exec_move P (new C') h ([], xs, 0, None) ta h' (stk', loc', pc', xcp')`
  from wf `P,Env,h \<turnstile>1 new C' : T` obtain FDTs
    where FDTs: "P \<turnstile> C' has_fields FDTs" by(auto dest: wf_Fields_Ex)
  have \<tau>: "\<not> \<tau>move2 (new C') 0 None" "\<not> \<tau>move1 (new C')" by(auto elim: \<tau>move2.cases \<tau>move1.cases)
  show ?case
  proof(cases "new_Addr h")
    case None
    have "P,new C',n,h \<turnstile> (THROW OutOfMemory, xs) \<leftrightarrow> ([], xs, 0, \<lfloor>addr_of_sys_xcpt OutOfMemory\<rfloor>)"
      by(rule bisim1NewThrow)
    with exec None \<tau> show ?thesis
      by(fastsimp intro: \<tau>Red_refl Red1NewFail elim!: exec_meth.cases simp add: exec_move_def)
  next
    case (Some a)
    have "P,new C',n,h(a \<mapsto> blank (compP2 P) C') \<turnstile> (addr a, xs) \<leftrightarrow> ([Addr a], xs, length (compE2 (new C')), None)"
      by(rule bisim1Val2) auto
    with exec Some \<tau> FDTs show ?thesis
      by(fastsimp elim!: exec_meth.cases intro: Red1New \<tau>Red_refl simp add: blank_def compP2_def exec_move_def)
  qed
next
  case (bisim1NewThrow C' n xs)
  from `?exec (new C') [] xs 0 \<lfloor>addr_of_sys_xcpt OutOfMemory\<rfloor> stk' loc' pc' xcp'`
  have False by(auto elim: exec_meth.cases simp add: exec_move_def)
  thus ?case ..
next
  case (bisim1NewArray e n e' xs stk loc pc xcp U)
  note IH = `\<And>stk' loc' pc' xcp' Env' T. 
            \<lbrakk> ?exec e stk loc pc xcp stk' loc' pc' xcp'; n + max_vars e' \<le> length xs; P,Env,h \<turnstile>1 e' : T \<rbrakk>
             \<Longrightarrow> \<exists>e'' xs''. P, e, n, h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp') \<and> ?red e' xs e'' xs'' e pc xcp`
  note exec = `?exec (newA U\<lfloor>e\<rceil>) stk loc pc xcp stk' loc' pc' xcp'`
  note bisim = `P,e,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note len = `n + max_vars (newA U\<lfloor>e'\<rceil>) \<le> length xs`
  from `P,Env,h \<turnstile>1 newA U\<lfloor>e'\<rceil> : T` obtain T' where wt: "P,Env,h \<turnstile>1 e' : T'" by auto
  from bisim have pc: "pc \<le> length (compE2 e)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e)")
    case True
    with exec have exec': "?exec e stk loc pc xcp stk' loc' pc' xcp'"
      by(auto simp add: exec_move_newArray)
    from True have "\<tau>move2 (newA U\<lfloor>e\<rceil>) pc xcp = \<tau>move2 e pc xcp"
      by(auto intro: \<tau>move2NewArray)
    with IH[OF exec' _ wt] len show ?thesis
      by(fastsimp intro: bisim1_bisims1.bisim1NewArray bisim1_bsok New1ArrayRed)
  next
    case False
    with pc have [simp]: "pc = length (compE2 e)" by simp
    with bisim obtain v where stk: "stk = [v]" and xcp: "xcp = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with bisim pc len have red: "\<tau>Red P h e' xs (Val v) loc" by(auto intro: bisim1_Val_\<tau>Red)
    hence "\<tau>Red P h (newA U\<lfloor>e'\<rceil>) xs (newA U\<lfloor>Val v\<rceil>) loc" by auto
    moreover have \<tau>: "\<not> \<tau>move2 (newA U\<lfloor>e\<rceil>) pc None"
      by(auto elim: \<tau>move2.cases dest: \<tau>move2_pc_length_compE2)
    moreover have "\<not> \<tau>move1 (newA U\<lfloor>Val v\<rceil>)" by auto
    moreover from exec stk xcp obtain I
      where [simp]: "v = Intg I" by(auto elim!: exec_meth.cases simp add: exec_move_def)
    have "\<exists>ta' e''. P,newA U\<lfloor>e\<rceil>,n,h' \<turnstile> (e'',loc) \<leftrightarrow> (stk', loc', pc', xcp') \<and> P \<turnstile>1 \<langle>newA U\<lfloor>Val v\<rceil>,(h, loc)\<rangle> -ta'\<rightarrow> \<langle>e'',(h', loc)\<rangle> \<and> ta_bisim (wbisim1 P) ta' ta"
    proof(cases "I < 0")
      case True with exec stk xcp `bsok e n` show ?thesis
	by(fastsimp elim!: exec_meth.cases intro: bisim1NewArrayNegative Red1NewArrayNegative simp add: exec_move_def)
    next
      case False
      show ?thesis
      proof(cases "new_Addr h")
	case None
	with False exec stk xcp `bsok e n` show ?thesis
	  by(fastsimp elim!: exec_meth.cases intro: bisim1NewArrayFail Red1NewArrayFail simp add: exec_move_def)
      next
	case (Some a)
	from `bsok e n` have "P,newA U\<lfloor>e\<rceil>,n,h' \<turnstile> (addr a, loc) \<leftrightarrow> ([Addr a], loc, length (compE2 (newA U\<lfloor>e\<rceil>)), None)"
	  by -(rule bisim1Val2, auto)
	with False Some exec stk xcp `bsok e n` show ?thesis
	  by(fastsimp elim!: exec_meth.cases intro: Red1NewArray simp add: exec_move_def)
      qed
    qed
    ultimately show ?thesis using exec stk xcp by fastsimp
  qed
next
  case (bisim1NewArrayThrow e n a xs stk loc pc U)
  note exec = `?exec (newA U\<lfloor>e\<rceil>) stk loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  note bisim = `P,e,n,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)`
  from bisim have pc: "pc < length (compE2 e)" by(auto dest: bisim1_ThrowD)
  from bisim have "match_ex_table (compP2 P) (cname_of h a) (0 + pc) (compxE2 e 0 0) = None"
    unfolding compP2_def by(rule bisim1_xcp_Some_not_caught)
  with exec pc have False by (auto elim!: exec_meth.cases simp add: exec_move_def)
  thus ?case ..
next
  case (bisim1NewArrayNegative e n U xs v)
  note exec = `?exec (newA U\<lfloor>e\<rceil>) [v] xs (length (compE2 e)) \<lfloor>addr_of_sys_xcpt NegativeArraySize\<rfloor> stk' loc' pc' xcp'`
  hence False by(auto elim!: exec_meth.cases dest: match_ex_table_pc_length_compE2 simp add: exec_move_def)
  thus ?case ..
next
  case (bisim1NewArrayFail e n U xs v)
  note exec = `?exec (newA U\<lfloor>e\<rceil>) [v] xs (length (compE2 e)) \<lfloor>addr_of_sys_xcpt OutOfMemory\<rfloor> stk' loc' pc' xcp'`
  hence False by(auto elim!: exec_meth.cases dest: match_ex_table_pc_length_compE2 simp add: exec_move_def)
  thus ?case ..
next
  case (bisim1Cast e n e' xs stk loc pc xcp U)
  note IH = `\<And>stk' loc' pc' xcp' Env' T. 
            \<lbrakk> ?exec e stk loc pc xcp stk' loc' pc' xcp'; n + max_vars e' \<le> length xs; P,Env,h \<turnstile>1 e' : T \<rbrakk>
             \<Longrightarrow> \<exists>e'' xs''. P, e, n, h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp') \<and> ?red e' xs e'' xs'' e pc xcp`
  note exec = `?exec (Cast U e) stk loc pc xcp stk' loc' pc' xcp'`
  note bisim = `P,e,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note len = `n + max_vars (Cast U e') \<le> length xs`
  from `P,Env,h \<turnstile>1 Cast U e' : T` obtain T' where wt: "P,Env,h \<turnstile>1 e' : T'" by auto
  from bisim have pc: "pc \<le> length (compE2 e)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e)")
    case True
    with exec have exec': "?exec e stk loc pc xcp stk' loc' pc' xcp'" by(auto simp add: exec_move_Cast)
    from True have "\<tau>move2 (Cast U e) pc xcp = \<tau>move2 e pc xcp" by(auto intro: \<tau>move2Cast)
    with IH[OF exec' _ wt] len show ?thesis
      by(fastsimp intro: bisim1_bisims1.bisim1Cast bisim1_bsok Cast1Red)
  next
    case False
    with pc have [simp]: "pc = length (compE2 e)" by simp
    with bisim obtain v where stk: "stk = [v]" and xcp: "xcp = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with bisim pc len have red: "\<tau>Red P h e' xs (Val v) loc" by(auto intro: bisim1_Val_\<tau>Red)
    hence "\<tau>Red P h (Cast U e') xs (Cast U (Val v)) loc" by auto
    moreover have \<tau>: "\<not> \<tau>move2 (Cast U e) pc None"
      by(auto elim: \<tau>move2.cases dest: \<tau>move2_pc_length_compE2)
    moreover have "\<not> \<tau>move1 (Cast U (Val v))" by auto
    moreover from bisim stk xcp wt have wt': "P,Env,h \<turnstile>1 Val v : T'"
      by(auto dest: bisim1_length_compE2_WTrt_eq)
    have "\<exists>ta' e''. P,Cast U e,n,h' \<turnstile> (e'',loc) \<leftrightarrow> (stk', loc', pc', xcp') \<and> P \<turnstile>1 \<langle>Cast U (Val v),(h, loc)\<rangle> -ta'\<rightarrow> \<langle>e'',(h', loc)\<rangle> \<and> ta_bisim (wbisim1 P) ta' ta"
    proof(cases "cast_ok P U h v")
      case False with exec stk xcp `bsok e n` wt' show ?thesis
	by(fastsimp elim!: exec_meth.cases simp add: compP2_def cast_ok_def exec_move_def intro: bisim1CastFail Red1CastFail)
    next
      case True
      from `bsok e n` have "P,Cast U e,n,h' \<turnstile> (Val v, loc) \<leftrightarrow> ([v], loc, length (compE2 (Cast U e)), None)"
	  by -(rule bisim1Val2, auto)
      with exec stk xcp `bsok e n` wt' True show ?thesis
	by(fastsimp elim!: exec_meth.cases simp add: compP2_def cast_ok_def exec_move_def intro: Red1Cast)
    qed
    ultimately show ?thesis using exec stk xcp by fastsimp
  qed
next
  case (bisim1CastThrow e n a xs stk loc pc U)
  note exec = `?exec (Cast U e) stk loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  note bisim = `P,e,n,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)`
  from bisim have pc: "pc < length (compE2 e)" by(auto dest: bisim1_ThrowD)
  from bisim have "match_ex_table (compP2 P) (cname_of h a) (0 + pc) (compxE2 e 0 0) = None"
    unfolding compP2_def by(rule bisim1_xcp_Some_not_caught)
  with exec pc have False by (auto elim!: exec_meth.cases simp add: exec_move_def)
  thus ?case ..
next
  case (bisim1CastFail e n U xs v)
  note exec = `?exec (Cast U e) [v] xs (length (compE2 e)) \<lfloor>addr_of_sys_xcpt ClassCast\<rfloor> stk' loc' pc' xcp'`
  hence False by(auto elim!: exec_meth.cases dest: match_ex_table_pc_length_compE2 simp add: exec_move_def)
  thus ?case ..
next
  case (bisim1Val v n xs)
  from `?exec (Val v) [] xs 0 None stk' loc' pc' xcp'`
  have "stk' = [v]" "loc' = xs" "h' = h" "pc' = length (compE2 (Val v))" "xcp' = None"
    by(auto elim: exec_meth.cases simp add: exec_move_def)
  moreover have "P,Val v,n,h \<turnstile> (Val v, xs) \<leftrightarrow> ([v], xs, length (compE2 (Val v)), None)"
    by(rule bisim1Val2) auto
  moreover have "\<tau>move2 (Val v) 0 None" by(rule \<tau>move2Val)
  ultimately show ?case by(auto intro: \<tau>Red_refl)
next
  case (bisim1Var V n xs)
  note exec = `?exec (Var V) [] xs 0 None stk' loc' pc' xcp'`
  moreover note len = `n + max_vars (Var V) \<le> length xs`
  moreover have "\<not> \<tau>move2 (Var V) 0 None" "\<not> \<tau>move1 (Var V)"
    by(auto elim: \<tau>move2.cases \<tau>move1.cases simp add: exec_move_def)
  moreover have "P,Var V,n,h \<turnstile> (Val (xs ! V), xs) \<leftrightarrow> ([xs ! V], xs, length (compE2 (Var V)), None)"
    by(rule bisim1Val2) auto
  ultimately show ?case by(fastsimp elim!: exec_meth.cases intro: Red1Var \<tau>Red_refl simp add: exec_move_def)
next
  case (bisim1BinOp1 e1 n e1' xs stk loc pc xcp e2 bop)
  note IH1 = `\<And>stk' loc' pc' xcp' Env' T. 
             \<lbrakk> ?exec e1 stk loc pc xcp stk' loc' pc' xcp'; n + max_vars e1' \<le> length xs; P,Env,h \<turnstile>1 e1' : T \<rbrakk>
             \<Longrightarrow> \<exists>e'' xs''. P, e1, n, h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp') \<and> ?red e1' xs e'' xs'' e1 pc xcp`
  note IH2 = `\<And>xs stk' loc' pc' xcp' Env' T. 
             \<lbrakk> ?exec e2 [] xs 0 None stk' loc' pc' xcp'; n + max_vars e2 \<le> length xs; P,Env,h \<turnstile>1 e2 : T \<rbrakk>
             \<Longrightarrow> \<exists>e'' xs''. P, e2, n, h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp') \<and> ?red e2 xs e'' xs'' e2 0 None`
  note exec = `?exec (e1 \<guillemotleft>bop\<guillemotright> e2) stk loc pc xcp stk' loc' pc' xcp'`
  note bisim1 = `P,e1,n,h \<turnstile> (e1', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim2 = `P,e2,n,h \<turnstile> (e2, loc) \<leftrightarrow> ([], loc, 0, None)`
  note len = `n + max_vars (e1' \<guillemotleft>bop\<guillemotright> e2) \<le> length xs`
  from `P,Env,h \<turnstile>1 e1' \<guillemotleft>bop\<guillemotright> e2 : T` obtain T1 T2
    where wt1: "P,Env,h \<turnstile>1 e1' : T1" and wt2: "P,Env,h \<turnstile>1 e2 : T2" by auto
  from bisim1 have pc: "pc \<le> length (compE2 e1)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e1)")
    case True
    with exec have exec': "?exec e1 stk loc pc xcp stk' loc' pc' xcp'" by(auto simp add: exec_move_BinOp1)
    from True have \<tau>: "\<tau>move2 (e1 \<guillemotleft>bop\<guillemotright> e2) pc xcp = \<tau>move2 e1 pc xcp" by(auto intro: \<tau>move2BinOp1)
    with IH1[OF exec' _ wt1] bisim2 len obtain e'' xs''
      where bisim': "P,e1,n,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp')"
      and red: "?red e1' xs e'' xs'' e1 pc xcp" by auto
    from bisim' `bsok e2 n` have "P,e1 \<guillemotleft>bop\<guillemotright> e2,n,h' \<turnstile> (e'' \<guillemotleft>bop\<guillemotright> e2, xs'') \<leftrightarrow> (stk', loc', pc', xcp')"
      by(rule bisim1_bisims1.bisim1BinOp1)
    with red \<tau> show ?thesis by(fastsimp intro: Bin1OpRed1)
  next
    case False
    with pc have pc: "pc = length (compE2 e1)" by auto
    with bisim1 obtain v where e1': "is_val e1' \<longrightarrow> e1' = Val v" 
      and stk: "stk = [v]" and xcp: "xcp = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with bisim1 pc len have rede1': "\<tau>Red P h e1' xs (Val v) loc" by(auto intro: bisim1_Val_\<tau>Red)
    hence "\<tau>Red P h (e1' \<guillemotleft>bop\<guillemotright> e2) xs (Val v \<guillemotleft>bop\<guillemotright> e2) loc" by auto
    moreover from pc exec stk xcp
    have "exec_meth (compP2 P) (compE2 (e1 \<guillemotleft>bop\<guillemotright> e2)) (compxE2 (e1 \<guillemotleft>bop\<guillemotright> e2) 0 0) h ([] @ [v], loc, length (compE2 e1) + 0, None) ta h' (stk', loc', pc', xcp')"
      by(simp add: compxE2_size_convs compxE2_stack_xlift_convs exec_move_def)
    hence exec': "exec_meth (compP2 P) (compE2 e2) (stack_xlift (length [v]) (compxE2 e2 0 0)) h ([] @ [v], loc, 0, None) ta h' (stk', loc', pc' - length (compE2 e1), xcp')"
      and pc': "pc' \<ge> length (compE2 e1)" by(safe dest!: BinOp_exec2D)simp_all
    then obtain PC' where PC': "pc' = length (compE2 e1) + PC'"
      by -(rule that[where PC'="pc' - length (compE2 e1)"], simp)
    from exec' bisim2 obtain stk'' where stk': "stk' = stk'' @ [v]"
      and exec'': "exec_move P e2 h ([], loc, 0, None) ta h' (stk'', loc', pc' - length (compE2 e1), xcp')"
      by(unfold exec_move_def)(drule (1) exec_meth_stk_split, auto)
    from pc xcp have \<tau>: "\<tau>move2 (e1 \<guillemotleft>bop\<guillemotright> e2) (length (compE2 e1)) None = \<tau>move2 e2 0 None"
      by(auto intro: \<tau>move2_BinOp2D dest: \<tau>move2BinOp2)
    from bisim1 have "length xs = length loc" by(rule bisim1_length_xs)
    with IH2[OF exec'' _ wt2] len obtain e'' xs''
      where bisim': "P,e2,n,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk'', loc', pc' - length (compE2 e1), xcp')"
      and red: "?red e2 loc e'' xs'' e2 0 None" by auto
    from bisim' `bsok e1 n`
    have "P,e1 \<guillemotleft>bop\<guillemotright> e2,n,h' \<turnstile> (Val v \<guillemotleft>bop\<guillemotright> e'', xs'') \<leftrightarrow> (stk'' @ [v], loc', length (compE2 e1) + (pc' - length (compE2 e1)), xcp')"
      by(rule bisim1_bisims1.bisim1BinOp2)
    moreover from red \<tau> have "?red (Val v \<guillemotleft>bop\<guillemotright> e2) loc (Val v \<guillemotleft>bop\<guillemotright> e'') xs'' (e1 \<guillemotleft>bop\<guillemotright> e2) (length (compE2 e1)) None"
      by(fastsimp intro: Bin1OpRed2)
    ultimately show ?thesis using \<tau> stk' pc xcp pc' PC' bisim1 bisim2 rede1' e1'
      by(fastsimp elim!: \<tau>Red_trans intro: \<tau>Red_refl)
   qed
next
  case (bisim1BinOp2 e2 n e2' xs stk loc pc xcp e1 bop v1)
  note IH2 = `\<And>stk' loc' pc' xcp' Env' T. 
             \<lbrakk> ?exec e2 stk loc pc xcp stk' loc' pc' xcp'; n + max_vars e2' \<le> length xs; P,Env,h \<turnstile>1 e2' : T \<rbrakk>
             \<Longrightarrow> \<exists>e'' xs''. P, e2, n, h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp') \<and> ?red e2' xs e'' xs'' e2 pc xcp`
  note exec = `?exec (e1 \<guillemotleft>bop\<guillemotright> e2) (stk @ [v1]) loc (length (compE2 e1) + pc) xcp stk' loc' pc' xcp'`
  note bisim1 = `P,e1,n,h \<turnstile> (e1, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim2 = `P,e2,n,h \<turnstile> (e2', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note len = `n + max_vars (Val v1 \<guillemotleft>bop\<guillemotright> e2') \<le> length xs`
  note wt = `P,Env,h \<turnstile>1 Val v1 \<guillemotleft>bop\<guillemotright> e2' : T`
  then obtain T1 T2 where wt1: "P,Env,h \<turnstile>1 Val v1 : T1" and wt2: "P,Env,h \<turnstile>1 e2' : T2" by auto
  from bisim2 have pc: "pc \<le> length (compE2 e2)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e2)")
    case True
    with exec have exec': "exec_meth (compP2 P) (compE2 e2) (stack_xlift (length [v1]) (compxE2 e2 0 0)) h (stk @ [v1], loc, pc, xcp) ta h' (stk', loc', pc' - length (compE2 e1), xcp')"
      and pc': "pc' \<ge> length (compE2 e1)"
      by(unfold exec_move_def)(safe dest!: BinOp_exec2D)
    from exec' bisim2 obtain stk'' where stk': "stk' = stk'' @ [v1]"
      and exec'': "exec_move P e2 h (stk, loc, pc, xcp) ta h' (stk'', loc', pc' - length (compE2 e1), xcp')"
      by -(drule (1) exec_meth_stk_split, auto simp add: exec_move_def)
    from True have \<tau>: "\<tau>move2 (e1 \<guillemotleft>bop\<guillemotright> e2) (length (compE2 e1) + pc) xcp = \<tau>move2 e2 pc xcp"
      by(auto intro: \<tau>move2_BinOp2D dest: \<tau>move2BinOp2)
    from IH2[OF exec'' _ wt2] len obtain e'' xs''
      where bisim': "P,e2,n,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk'', loc', pc' - length (compE2 e1), xcp')"
      and red: "?red e2' xs e'' xs'' e2 pc xcp" by auto
    from bisim' bisim1 have "P,e1 \<guillemotleft>bop\<guillemotright> e2,n,h' \<turnstile> (Val v1 \<guillemotleft>bop\<guillemotright> e'', xs'') \<leftrightarrow> (stk'' @ [v1], loc', length (compE2 e1) + (pc' - length (compE2 e1)), xcp')"
      by(rule bisim1_bisims1.bisim1BinOp2[OF _ bisim1_bsok])
    with red \<tau> stk' pc' True show ?thesis
      by(fastsimp intro: Bin1OpRed2)
  next
    case False
    with pc have [simp]: "pc = length (compE2 e2)" by simp
    with bisim2 obtain v2 where e2': "is_val e2' \<longrightarrow> e2' = Val v2" 
      and stk: "stk = [v2]" and xcp: "xcp = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with bisim2 pc len have red: "\<tau>Red P h e2' xs (Val v2) loc" by(auto intro: bisim1_Val_\<tau>Red)
    hence "\<tau>Red P h (Val v1 \<guillemotleft>bop\<guillemotright> e2') xs (Val v1 \<guillemotleft>bop\<guillemotright> Val v2) loc" by auto
    moreover from bisim2 stk xcp wt have "bop = Add \<Longrightarrow> P,Env,h \<turnstile>1 Val v2 : Integer"
      by(auto dest: bisim1_length_compE2_WTrt_eq)
    moreover have \<tau>: "\<not> \<tau>move2 (e1 \<guillemotleft>bop\<guillemotright> e2) (length (compE2 e1) + length (compE2 e2)) None"
      by(fastsimp elim: \<tau>move2.cases dest: \<tau>move2_pc_length_compE2)
    moreover from bisim1 bisim2 have "bsok (e1 \<guillemotleft>bop\<guillemotright> e2) n" by(auto dest!: bisim1_bsok)
    hence "P,e1 \<guillemotleft>bop\<guillemotright> e2,n,h \<turnstile> (Val (case bop of Eq \<Rightarrow> Bool (v1 = v2) | Add \<Rightarrow> Intg (the_Intg v1 + the_Intg v2)), loc) \<leftrightarrow> ([(case bop of Eq \<Rightarrow> Bool (v1 = v2) | Add \<Rightarrow> Intg (the_Intg v1 + the_Intg v2))], loc, length (compE2 (e1 \<guillemotleft>bop\<guillemotright> e2)), None)"
      by(rule bisim1Val2)
    ultimately show ?thesis using exec xcp stk wt
      by(fastsimp elim!: exec_meth.cases split: bop.splits intro: Red1BinOp simp add: exec_move_def)
  qed
next
  case (bisim1BinOpThrow1 e1 n a xs stk loc pc e2 bop)
  note exec = `?exec (e1 \<guillemotleft>bop\<guillemotright> e2) stk loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  note bisim1 = `P,e1,n,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)`
  from bisim1 have pc: "pc < length (compE2 e1)" by(auto dest: bisim1_ThrowD)
  from bisim1 have "match_ex_table (compP2 P) (cname_of h a) (0 + pc) (compxE2 e1 0 0) = None"
    unfolding compP2_def by(rule  bisim1_xcp_Some_not_caught)
  with exec pc have False by(auto elim!: exec_meth.cases simp add: match_ex_table_not_pcs_None exec_move_def)
  thus ?case ..
next
  case (bisim1BinOpThrow2 e2 n a xs stk loc pc e1 bop v1)
  note exec = `?exec (e1 \<guillemotleft>bop\<guillemotright> e2) (stk @ [v1]) loc (length (compE2 e1) + pc) \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  note bisim2 = `P,e2,n,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)`
  hence "match_ex_table (compP2 P) (cname_of h a) (length (compE2 e1) + pc) (compxE2 e2 (length (compE2 e1)) 0) = None"
    unfolding compP2_def by(rule bisim1_xcp_Some_not_caught)
  with exec have False
    apply(auto elim!: exec_meth.cases simp add: match_ex_table_append_not_pcs exec_move_def)
    apply(auto simp only: compxE2_size_convs compxE2_stack_xlift_convs match_ex_table_stack_xlift_eq_Some_conv)
    done
  thus ?case ..
next
  case (bisim1LAss1 e n e' xs stk loc pc xcp V)
  note IH = `\<And>stk' loc' pc' xcp' Env' T. 
            \<lbrakk> ?exec e stk loc pc xcp stk' loc' pc' xcp'; n + max_vars e' \<le> length xs; P,Env,h \<turnstile>1 e' : T \<rbrakk>
             \<Longrightarrow> \<exists>e'' xs''. P, e, n, h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp') \<and> ?red e' xs e'' xs'' e pc xcp`
  note exec = `?exec (V := e) stk loc pc xcp stk' loc' pc' xcp'`
  note bisim = `P,e,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note len = `n + max_vars (V := e') \<le> length xs`
  from `P,Env,h \<turnstile>1 V := e' : T` obtain T' where wt: "P,Env,h \<turnstile>1 e' : T'" by auto
  from bisim have pc: "pc \<le> length (compE2 e)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e)")
    case True
    with exec have exec': "?exec e stk loc pc xcp stk' loc' pc' xcp'" by(auto simp add: exec_move_LAss)
    from True have "\<tau>move2 (V := e) pc xcp = \<tau>move2 e pc xcp" by(auto intro: \<tau>move2LAss)
    with IH[OF exec' _ wt] len show ?thesis
      by(fastsimp intro: bisim1_bisims1.bisim1LAss1 bisim1_bsok LAss1Red)
  next
    case False
    with pc have [simp]: "pc = length (compE2 e)" by simp
    with bisim obtain v where stk: "stk = [v]" and xcp: "xcp = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with bisim pc len have red: "\<tau>Red P h e' xs (Val v) loc" by(auto intro: bisim1_Val_\<tau>Red)
    hence "\<tau>Red P h (V := e') xs (V := Val v) loc" by auto
    moreover have \<tau>: "\<not> \<tau>move2 (V := e) pc None"
      by(auto elim: \<tau>move2.cases dest: \<tau>move2_pc_length_compE2)
    moreover have "\<not> \<tau>move1 (V := Val v)" by auto
    moreover from bisim
    have "P,(V := e),n,h \<turnstile> (unit, loc[V := v]) \<leftrightarrow> ([], loc[V := v], Suc (length (compE2 e)), None)"
      by(rule bisim1LAss2[OF bisim1_bsok])
    ultimately show ?thesis using exec stk xcp
      by(fastsimp elim!: exec_meth.cases intro: Red1LAss simp add: exec_move_def)
  qed
next
  case (bisim1LAss2 e n V xs)
  note bisim = `P,e,n,h \<turnstile> (e, xs) \<leftrightarrow> ([], xs, 0, None)`
  note exec = `?exec (V := e) [] xs (Suc (length (compE2 e))) None stk' loc' pc' xcp'`
  hence "stk' = [Unit]" "loc' = xs" "pc' = length (compE2 (V := e))" "xcp' = None" "h' = h"
    by(auto elim!: exec_meth.cases simp add: exec_move_def)
  moreover have "\<tau>move2 (V := e) (Suc (length (compE2 e))) None"
    by(rule \<tau>move2LAssRed)
  moreover from bisim
  have "P,V:=e,n,h' \<turnstile> (unit, xs) \<leftrightarrow> ([Unit], xs, length (compE2 (V := e)), None)"
    by(rule bisim1Val2[OF bisim1_bsok[OF bisim1LAss1]])
  ultimately show ?case by(auto intro: \<tau>Red_refl)
next
  case (bisim1LAssThrow e n a xs stk loc pc V)
  note exec = `?exec (V := e) stk loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  note bisim = `P,e,n,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)`
  from bisim have pc: "pc < length (compE2 e)" by(auto dest: bisim1_ThrowD)
  from bisim have "match_ex_table (compP2 P) (cname_of h a) (0 + pc) (compxE2 e 0 0) = None"
    unfolding compP2_def by(rule  bisim1_xcp_Some_not_caught)
  with exec pc have False by (auto elim!: exec_meth.cases simp add: exec_move_def)
  thus ?case ..
next
  case (bisim1AAcc1 a n a' xs stk loc pc xcp i)
  note IH1 = `\<And>stk' loc' pc' xcp' Env' T. 
             \<lbrakk> ?exec a stk loc pc xcp stk' loc' pc' xcp'; n + max_vars a' \<le> length xs; P,Env,h \<turnstile>1 a' : T \<rbrakk>
             \<Longrightarrow> \<exists>e'' xs''. P, a, n, h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp') \<and> ?red a' xs e'' xs'' a pc xcp`
  note IH2 = `\<And>xs stk' loc' pc' xcp' Env' T. 
             \<lbrakk> ?exec i [] xs 0 None stk' loc' pc' xcp'; n + max_vars i \<le> length xs; P,Env,h \<turnstile>1 i : T \<rbrakk>
             \<Longrightarrow> \<exists>e'' xs''. P, i, n, h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp') \<and> ?red i xs e'' xs'' i 0 None`
  note exec = `?exec (a\<lfloor>i\<rceil>) stk loc pc xcp stk' loc' pc' xcp'`
  note bisim1 = `P,a,n,h \<turnstile> (a', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim2 = `P,i,n,h \<turnstile> (i, loc) \<leftrightarrow> ([], loc, 0, None)`
  note len = `n + max_vars (a'\<lfloor>i\<rceil>) \<le> length xs`
  from `P,Env,h \<turnstile>1 a'\<lfloor>i\<rceil> : T` obtain T1
    where wt1: "P,Env,h \<turnstile>1 a' : T1" and wt2: "P,Env,h \<turnstile>1 i : Integer" by auto
  from bisim1 have pc: "pc \<le> length (compE2 a)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 a)")
    case True
    with exec have exec': "?exec a stk loc pc xcp stk' loc' pc' xcp'" by(auto simp add: exec_move_AAcc1)
    from True have \<tau>: "\<tau>move2 (a\<lfloor>i\<rceil>) pc xcp = \<tau>move2 a pc xcp" by(auto intro: \<tau>move2AAcc1)
    with IH1[OF exec' _ wt1] len obtain e'' xs''
      where bisim': "P,a,n,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp')"
      and red: "?red a' xs e'' xs'' a pc xcp" by auto
    from bisim' `bsok i n` have "P,a\<lfloor>i\<rceil>,n,h' \<turnstile> (e''\<lfloor>i\<rceil>, xs'') \<leftrightarrow> (stk', loc', pc', xcp')" by(rule bisim1_bisims1.bisim1AAcc1)
    with red \<tau> show ?thesis by(fastsimp intro: AAcc1Red1)
  next
    case False
    with pc have pc: "pc = length (compE2 a)" by auto
    with bisim1 obtain v where a': "is_val a' \<longrightarrow> a' = Val v" 
      and stk: "stk = [v]" and xcp: "xcp = None" by(auto dest: bisim1_pc_length_compE2D)
    with bisim1 pc len have rede1': "\<tau>Red P h a' xs (Val v) loc" by(auto intro: bisim1_Val_\<tau>Red)
    hence "\<tau>Red P h (a'\<lfloor>i\<rceil>) xs (Val v\<lfloor>i\<rceil>) loc" by auto
    moreover from pc exec stk xcp
    have exec': "exec_meth (compP2 P) (compE2 a @ compE2 i @ [ALoad]) (compxE2 a 0 0 @ shift (length (compE2 a)) (stack_xlift (length [v]) (compxE2 i 0 0))) h ([] @ [v], loc, length (compE2 a) + 0, None) ta h' (stk', loc', pc', xcp')"
      by(simp add: compxE2_size_convs compxE2_stack_xlift_convs exec_move_def)
    hence "exec_meth (compP2 P) (compE2 i @ [ALoad]) (stack_xlift (length [v]) (compxE2 i 0 0)) h ([] @ [v], loc, 0, None) ta h' (stk', loc', pc' - length (compE2 a), xcp')"
      by(rule exec_meth_drop_xt) auto
    hence "exec_meth (compP2 P) (compE2 i) (stack_xlift (length [v]) (compxE2 i 0 0)) h ([] @ [v], loc, 0, None) ta h' (stk', loc', pc' - length (compE2 a), xcp')"
      by(rule exec_meth_take) simp
    with bisim2 obtain stk'' where stk': "stk' = stk'' @ [v]"
      and exec'': "exec_move P i h ([], loc, 0, None) ta h' (stk'', loc', pc' - length (compE2 a), xcp')"
      unfolding exec_move_def by(blast dest: exec_meth_stk_split)
    from pc xcp have \<tau>: "\<tau>move2 (a\<lfloor>i\<rceil>) (length (compE2 a)) None = \<tau>move2 i 0 None"
      by(auto intro: \<tau>move2_AAccD2 dest: \<tau>move2AAcc2)
    from bisim1 have "length xs = length loc" by(rule bisim1_length_xs)
    with IH2[OF exec'' _ wt2] len obtain e'' xs''
      where bisim': "P,i,n,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk'', loc', pc' - length (compE2 a), xcp')"
      and red: "?red i loc e'' xs'' i 0 None" by auto
    from bisim' `bsok a n`
    have "P,a\<lfloor>i\<rceil>,n,h' \<turnstile> (Val v\<lfloor>e''\<rceil>, xs'') \<leftrightarrow> (stk'' @ [v], loc', length (compE2 a) + (pc' - length (compE2 a)), xcp')"
      by(rule bisim1_bisims1.bisim1AAcc2)
    moreover from red \<tau> have "?red (Val v\<lfloor>i\<rceil>) loc (Val v\<lfloor>e''\<rceil>) xs'' (a\<lfloor>i\<rceil>) (length (compE2 a)) None"
      by(fastsimp intro: AAcc1Red2)
    moreover from exec' have "pc' \<ge> length (compE2 a)"
      by(rule exec_meth_drop_xt_pc) auto
    ultimately show ?thesis using \<tau> stk' pc xcp by(fastsimp elim!: \<tau>Red_trans intro: \<tau>Red_refl)
  qed
next
  case (bisim1AAcc2 i n i' xs stk loc pc xcp a v)
  note IH2 = `\<And>stk' loc' pc' xcp' Env' T. 
             \<lbrakk> ?exec i stk loc pc xcp stk' loc' pc' xcp'; n + max_vars i' \<le> length xs; P,Env,h \<turnstile>1 i' : T \<rbrakk>
             \<Longrightarrow> \<exists>e'' xs''. P, i, n, h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp') \<and> ?red i' xs e'' xs'' i pc xcp`
  note exec = `?exec (a\<lfloor>i\<rceil>) (stk @ [v]) loc (length (compE2 a) + pc) xcp stk' loc' pc' xcp'`
  note bisim2 = `P,i,n,h \<turnstile> (i', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note len = `n + max_vars (Val v\<lfloor>i'\<rceil>) \<le> length xs`
  note wt = `P,Env,h \<turnstile>1 Val v\<lfloor>i'\<rceil> : T`
  hence wt2: "P,Env,h \<turnstile>1 i' : Integer" by auto
  from bisim2 have pc: "pc \<le> length (compE2 i)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 i)")
    case True
    from exec have exec': "exec_meth (compP2 P) (compE2 a @ compE2 i @ [ALoad]) (compxE2 a 0 0 @ shift (length (compE2 a)) (stack_xlift (length [v]) (compxE2 i 0 0))) h (stk @ [v], loc, length (compE2 a) + pc, xcp) ta h' (stk', loc', pc', xcp')"
      by(simp add: shift_compxE2 stack_xlift_compxE2 exec_move_def)
    hence "exec_meth (compP2 P) (compE2 i @ [ALoad]) (stack_xlift (length [v]) (compxE2 i 0 0)) h (stk @ [v], loc, pc, xcp) ta h' (stk', loc', pc' - length (compE2 a), xcp')"
      by(rule exec_meth_drop_xt) auto
    hence "exec_meth (compP2 P) (compE2 i) (stack_xlift (length [v]) (compxE2 i 0 0)) h (stk @ [v], loc, pc, xcp) ta h' (stk', loc', pc' - length (compE2 a), xcp')"
      using True by(rule exec_meth_take)
    with bisim2 obtain stk'' where stk': "stk' = stk'' @ [v]"
      and exec'': "exec_move P i h (stk, loc, pc, xcp) ta h' (stk'', loc', pc' - length (compE2 a), xcp')"
      unfolding exec_move_def by(blast dest: exec_meth_stk_split)
    from True have \<tau>: "\<tau>move2 (a\<lfloor>i\<rceil>) (length (compE2 a) + pc) xcp = \<tau>move2 i pc xcp" by(auto intro: \<tau>move2AAcc2)
    moreover from IH2[OF exec'' _ wt2] len obtain e'' xs''
      where bisim': "P,i,n,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk'', loc', pc' - length (compE2 a), xcp')"
      and red: "?red i' xs e'' xs'' i pc xcp" by auto
    from bisim' `bsok a n` have "P,a\<lfloor>i\<rceil>,n,h' \<turnstile> (Val v\<lfloor>e''\<rceil>, xs'') \<leftrightarrow> (stk'' @ [v], loc', length (compE2 a) + (pc' - length (compE2 a)), xcp')"
      by(rule bisim1_bisims1.bisim1AAcc2)
    moreover from exec' have "pc' \<ge> length (compE2 a)"
      by(rule exec_meth_drop_xt_pc) auto
    ultimately show ?thesis using red \<tau> stk' True by(fastsimp intro: AAcc1Red2)
  next
    case False
    with pc have [simp]: "pc = length (compE2 i)" by simp
    with bisim2 obtain v2 where i': "is_val i' \<longrightarrow> i' = Val v2" 
      and stk: "stk = [v2]" and xcp: "xcp = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with bisim2 pc len have red: "\<tau>Red P h i' xs (Val v2) loc" by(auto intro: bisim1_Val_\<tau>Red)
    hence "\<tau>Red P h (Val v\<lfloor>i'\<rceil>) xs (Val v\<lfloor>Val v2\<rceil>) loc" by auto
    moreover have \<tau>: "\<not> \<tau>move2 (a\<lfloor>i\<rceil>) (length (compE2 a) + length (compE2 i)) None"
      by(fastsimp elim: \<tau>move2.cases dest: \<tau>move2_pc_length_compE2)
    moreover from `bsok a n` `bsok i n` have B: "bsok (a\<lfloor>i\<rceil>) n" by(auto)
    have "\<exists>ta' e''. P,a\<lfloor>i\<rceil>,n,h' \<turnstile> (e'',loc) \<leftrightarrow> (stk', loc', pc', xcp') \<and> P \<turnstile>1 \<langle>Val v\<lfloor>Val v2\<rceil>, (h, loc)\<rangle> -ta'\<rightarrow> \<langle>e'',(h', loc)\<rangle> \<and> ta_bisim (wbisim1 P) ta' ta"
    proof(cases "v = Null")
      case True with exec stk xcp `bsok a n` `bsok i n` show ?thesis
	by(fastsimp elim!: exec_meth.cases simp add: exec_move_def intro: bisim1AAccNull Red1AAccNull)
    next
      case False
      with wt obtain U el A where [simp]: "v = Addr A" and hA: "h A = \<lfloor>Arr U el\<rfloor>" by fastsimp
      from bisim2 stk xcp wt2 have "P,Env,h \<turnstile>1 Val v2 : Integer"
	by(auto dest: bisim1_length_compE2_WTrt_eq)
      then obtain I where [simp]: "v2 = Intg I" by auto
      show ?thesis
      proof(cases "0 \<le> I \<and> I < int (length el)")
	case True
	from B have "P,a\<lfloor>i\<rceil>,n,h' \<turnstile> (Val (el ! nat I),loc) \<leftrightarrow> ([el ! nat I], loc, length (compE2 (a\<lfloor>i\<rceil>)), None)"
	  by(rule bisim1Val2)
	with exec stk xcp True hA show ?thesis
	  by(fastsimp elim!: exec_meth.cases intro: Red1AAcc simp add: exec_move_def)
      next
	case False
	with exec stk xcp hA `bsok a n` `bsok i n` show ?thesis
	  by(fastsimp elim!: exec_meth.cases simp add: is_Ref_def exec_move_def intro: bisim1AAccBounds Red1AAccBounds)
      qed
    qed
    ultimately show ?thesis using exec xcp stk by fastsimp
  qed
next
  case (bisim1AAccThrow1 A n a xs stk loc pc i)
  note exec = `?exec (A\<lfloor>i\<rceil>) stk loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  note bisim1 = `P,A,n,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)`
  from bisim1 have pc: "pc < length (compE2 A)" by(auto dest: bisim1_ThrowD)
  from bisim1 have "match_ex_table (compP2 P) (cname_of h a) (0 + pc) (compxE2 A 0 0) = None"
    unfolding compP2_def by(rule bisim1_xcp_Some_not_caught)
  with exec pc have False
    by(auto elim!: exec_meth.cases simp add: match_ex_table_not_pcs_None exec_move_def)
  thus ?case ..
next
  case (bisim1AAccThrow2 i n a xs stk loc pc A v)
  note exec = `?exec (A\<lfloor>i\<rceil>) (stk @ [v]) loc (length (compE2 A) + pc) \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  note bisim2 = `P,i,n,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)`
  hence "match_ex_table (compP2 P) (cname_of h a) (length (compE2 A) + pc) (compxE2 i (length (compE2 A)) 0) = None"
    unfolding compP2_def by(rule bisim1_xcp_Some_not_caught)
  with exec have False
    apply(auto elim!: exec_meth.cases simp add: match_ex_table_append_not_pcs exec_move_def)
    apply(auto simp only: compxE2_size_convs compxE2_stack_xlift_convs match_ex_table_stack_xlift_eq_Some_conv)
    done
  thus ?case ..
next
  case (bisim1AAccNull a n i xs v)
  note exec = `?exec (a\<lfloor>i\<rceil>) [v, Null] xs (length (compE2 a) + length (compE2 i)) \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor> stk' loc' pc' xcp'`
  hence False
    by(auto elim!: exec_meth.cases simp add: match_ex_table_append_not_pcs compxE2_size_convs exec_move_def
               dest!: match_ex_table_shift_pcD match_ex_table_pc_length_compE2)
  thus ?case ..
next
  case (bisim1AAccBounds a n i xs v A)
  note exec = `?exec (a\<lfloor>i\<rceil>) [v, Addr A] xs (length (compE2 a) + length (compE2 i)) \<lfloor>addr_of_sys_xcpt ArrayIndexOutOfBounds\<rfloor> stk' loc' pc' xcp'`
  hence False
    by(auto elim!: exec_meth.cases simp add: match_ex_table_append_not_pcs compxE2_size_convs exec_move_def
               dest!: match_ex_table_shift_pcD match_ex_table_pc_length_compE2)
  thus ?case ..
next
  case (bisim1AAss1 a n a' xs stk loc pc xcp i e)
  note IH1 = `\<And>stk' loc' pc' xcp' Env' T. 
             \<lbrakk> ?exec a stk loc pc xcp stk' loc' pc' xcp'; n + max_vars a' \<le> length xs; P,Env,h \<turnstile>1 a' : T \<rbrakk>
             \<Longrightarrow> \<exists>e'' xs''. P, a, n, h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp') \<and> ?red a' xs e'' xs'' a pc xcp`
  note IH2 = `\<And>xs stk' loc' pc' xcp' Env' T. 
             \<lbrakk> ?exec i [] xs 0 None stk' loc' pc' xcp'; n + max_vars i \<le> length xs; P,Env,h \<turnstile>1 i : T \<rbrakk>
             \<Longrightarrow> \<exists>e'' xs''. P, i, n, h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp') \<and> ?red i xs e'' xs'' i 0 None`
  note exec = `?exec (a\<lfloor>i\<rceil> := e) stk loc pc xcp stk' loc' pc' xcp'`
  note bisim1 = `P,a,n,h \<turnstile> (a', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim2 = `P,i,n,h \<turnstile> (i, loc) \<leftrightarrow> ([], loc, 0, None)`
  note len = `n + max_vars (a'\<lfloor>i\<rceil> := e) \<le> length xs`
  from `P,Env,h \<turnstile>1 a'\<lfloor>i\<rceil> := e : T` obtain T1
    where wt1: "P,Env,h \<turnstile>1 a' : T1" and wt2: "P,Env,h \<turnstile>1 i : Integer" by auto
  from bisim1 have pc: "pc \<le> length (compE2 a)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 a)")
    case True
    with exec have exec': "?exec a stk loc pc xcp stk' loc' pc' xcp'" by(simp add: exec_move_AAss1)
    from True have \<tau>: "\<tau>move2 (a\<lfloor>i\<rceil> := e) pc xcp = \<tau>move2 a pc xcp" by(auto intro: \<tau>move2AAss1)
    with IH1[OF exec' _ wt1] len obtain e'' xs''
      where bisim': "P,a,n,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp')"
      and red: "?red a' xs e'' xs'' a pc xcp" by auto
    from bisim' `bsok i n` `bsok e n` have "P,a\<lfloor>i\<rceil> := e,n,h' \<turnstile> (e''\<lfloor>i\<rceil> := e, xs'') \<leftrightarrow> (stk', loc', pc', xcp')"
      by(rule bisim1_bisims1.bisim1AAss1)
    with red \<tau> show ?thesis by(fastsimp intro: AAss1Red1)
  next
    case False
    with pc have pc: "pc = length (compE2 a)" by auto
    with bisim1 obtain v where a': "is_val a' \<longrightarrow> a' = Val v" 
      and stk: "stk = [v]" and xcp: "xcp = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with bisim1 pc len have rede1': "\<tau>Red P h a' xs (Val v) loc" by(auto intro: bisim1_Val_\<tau>Red)
    hence "\<tau>Red P h (a'\<lfloor>i\<rceil> := e) xs (Val v\<lfloor>i\<rceil> := e) loc" by auto
    moreover from pc exec stk xcp
    have exec': "exec_meth (compP2 P) (compE2 a @ compE2 i @ compE2 e @ [AStore, Push Unit]) (compxE2 a 0 0 @ shift (length (compE2 a)) (stack_xlift (length [v]) (compxE2 i 0 0) @ shift (length (compE2 i)) (compxE2 e 0 (Suc (Suc 0))))) h ([] @ [v], loc, length (compE2 a) + 0, None) ta h' (stk', loc', pc', xcp')"
      by(simp add: compxE2_size_convs compxE2_stack_xlift_convs exec_move_def)
    hence "exec_meth (compP2 P) (compE2 i @ compE2 e @ [AStore, Push Unit]) (stack_xlift (length [v]) (compxE2 i 0 0) @ shift (length (compE2 i)) (compxE2 e 0 (Suc (Suc 0)))) h ([] @ [v], loc, 0, None) ta h' (stk', loc', pc' - length (compE2 a), xcp')"
      by(rule exec_meth_drop_xt) auto
    hence "exec_meth (compP2 P) (compE2 i) (stack_xlift (length [v]) (compxE2 i 0 0)) h ([] @ [v], loc, 0, None) ta h' (stk', loc', pc' - length (compE2 a), xcp')"
      by(rule exec_meth_take_xt) simp
    with bisim2 obtain stk'' where stk': "stk' = stk'' @ [v]"
      and exec'': "exec_move P i h ([], loc, 0, None) ta h' (stk'', loc', pc' - length (compE2 a), xcp')"
      unfolding exec_move_def by(blast dest: exec_meth_stk_split)
    from pc xcp have \<tau>: "\<tau>move2 (a\<lfloor>i\<rceil>:= e) (length (compE2 a)) None = \<tau>move2 i 0 None"
      by(auto intro: \<tau>move2_AAssD2 dest: \<tau>move2AAss2)
    from bisim1 have "length xs = length loc" by(rule bisim1_length_xs)
    with IH2[OF exec'' _ wt2] len obtain e'' xs''
      where bisim': "P,i,n,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk'', loc', pc' - length (compE2 a), xcp')"
      and red: "?red i loc e'' xs'' i 0 None" by auto
    from bisim' `bsok a n` `bsok e n`
    have "P,a\<lfloor>i\<rceil> := e,n,h' \<turnstile> (Val v\<lfloor>e''\<rceil> := e, xs'') \<leftrightarrow> (stk'' @ [v], loc', length (compE2 a) + (pc' - length (compE2 a)), xcp')"
      by(rule bisim1_bisims1.bisim1AAss2)
    moreover from red \<tau> have "?red (Val v\<lfloor>i\<rceil> := e) loc (Val v\<lfloor>e''\<rceil> := e) xs'' (a\<lfloor>i\<rceil> := e) (length (compE2 a)) None"
      by(fastsimp intro: AAss1Red2)
    moreover from exec' have "pc' \<ge> length (compE2 a)"
      by(rule exec_meth_drop_xt_pc) auto
    ultimately show ?thesis using \<tau> stk' pc xcp by(fastsimp elim!: \<tau>Red_trans intro: \<tau>Red_refl)
  qed
next
  case (bisim1AAss2 i n i' xs stk loc pc xcp a e v)
  note IH2 = `\<And>stk' loc' pc' xcp' Env' T. 
             \<lbrakk> ?exec i stk loc pc xcp stk' loc' pc' xcp'; n + max_vars i' \<le> length xs; P,Env,h \<turnstile>1 i' : T \<rbrakk>
             \<Longrightarrow> \<exists>e'' xs''. P, i, n, h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp') \<and> ?red i' xs e'' xs'' i pc xcp`
  note IH3 = `\<And>xs stk' loc' pc' xcp' Env' T. 
             \<lbrakk> ?exec e [] xs 0 None stk' loc' pc' xcp'; n + max_vars e \<le> length xs; P,Env,h \<turnstile>1 e : T \<rbrakk>
             \<Longrightarrow> \<exists>e'' xs''. P, e, n, h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp') \<and> ?red e xs e'' xs'' e 0 None`
  note exec = `?exec (a\<lfloor>i\<rceil> := e) (stk @ [v]) loc (length (compE2 a) + pc) xcp stk' loc' pc' xcp'`
  note bisim2 = `P,i,n,h \<turnstile> (i', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim3 = `P,e,n,h \<turnstile> (e, loc) \<leftrightarrow> ([], loc, 0, None)`
  note len = `n + max_vars (Val v\<lfloor>i'\<rceil> := e) \<le> length xs`
  note wt = `P,Env,h \<turnstile>1 Val v\<lfloor>i'\<rceil> := e : T`
  then obtain T3 where wt2: "P,Env,h \<turnstile>1 i' : Integer" and wt3: "P,Env,h \<turnstile>1 e : T3" by auto
  from bisim2 have pc: "pc \<le> length (compE2 i)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 i)")
    case True
    from exec have exec': "exec_meth (compP2 P) (compE2 a @ compE2 i @ compE2 e @ [AStore, Push Unit]) (compxE2 a 0 0 @ shift (length (compE2 a)) (stack_xlift (length [v]) (compxE2 i 0 0) @ shift (length (compE2 i)) (compxE2 e 0 (Suc (Suc 0))))) h (stk @ [v], loc, length (compE2 a) + pc, xcp) ta h' (stk', loc', pc', xcp')"
      by(simp add: shift_compxE2 stack_xlift_compxE2 add_ac exec_move_def)
    hence "exec_meth (compP2 P) (compE2 i @ compE2 e @ [AStore, Push Unit]) (stack_xlift (length [v]) (compxE2 i 0 0) @ shift (length (compE2 i)) (compxE2 e 0 (Suc (Suc 0)))) h (stk @ [v], loc, pc, xcp) ta h' (stk', loc', pc' - length (compE2 a), xcp')"
      by(rule exec_meth_drop_xt) auto
    hence "exec_meth (compP2 P) (compE2 i) (stack_xlift (length [v]) (compxE2 i 0 0)) h (stk @ [v], loc, pc, xcp) ta h' (stk', loc', pc' - length (compE2 a), xcp')"
      using True by(rule exec_meth_take_xt)
    with bisim2 obtain stk'' where stk': "stk' = stk'' @ [v]"
      and exec'': "exec_move P i h (stk, loc, pc, xcp) ta h' (stk'', loc', pc' - length (compE2 a), xcp')"
      unfolding exec_move_def by(blast dest: exec_meth_stk_split)
    from True have \<tau>: "\<tau>move2 (a\<lfloor>i\<rceil> := e) (length (compE2 a) + pc) xcp = \<tau>move2 i pc xcp"
      by(auto intro: \<tau>move2AAss2)
    moreover from IH2[OF exec'' _ wt2] len obtain e'' xs''
      where bisim': "P,i,n,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk'', loc', pc' - length (compE2 a), xcp')"
      and red: "?red i' xs e'' xs'' i pc xcp" by auto
    from bisim' `bsok a n` `bsok e n` 
    have "P,a\<lfloor>i\<rceil> := e,n,h' \<turnstile> (Val v\<lfloor>e''\<rceil> := e, xs'') \<leftrightarrow> (stk'' @ [v], loc', length (compE2 a) + (pc' - length (compE2 a)), xcp')"
      by(rule bisim1_bisims1.bisim1AAss2)
    moreover from exec' have "pc' \<ge> length (compE2 a)"
      by(rule exec_meth_drop_xt_pc) auto
    ultimately show ?thesis using red \<tau> stk' True by(fastsimp intro: AAss1Red2)
  next
    case False
    with pc have [simp]: "pc = length (compE2 i)" by simp
    with bisim2 obtain v2 where i': "is_val i' \<longrightarrow> i' = Val v2" 
      and stk: "stk = [v2]" and xcp: "xcp = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with bisim2 pc len have red: "\<tau>Red P h i' xs (Val v2) loc" by(auto intro: bisim1_Val_\<tau>Red)
    hence "\<tau>Red P h (Val v\<lfloor>i'\<rceil> := e) xs (Val v\<lfloor>Val v2\<rceil> := e) loc" by auto
    moreover from pc exec stk xcp
    have exec': "exec_meth (compP2 P) ((compE2 a @ compE2 i) @ compE2 e @ [AStore, Push Unit]) ((compxE2 a 0 0 @ compxE2 i (length (compE2 a)) (Suc 0)) @ shift (length (compE2 a @ compE2 i)) (stack_xlift (length [v2, v]) (compxE2 e 0 0))) h ([] @ [v2, v], loc, length (compE2 a @ compE2 i) + 0, None) ta h' (stk', loc', pc', xcp')"
      by(simp add: compxE2_size_convs compxE2_stack_xlift_convs exec_move_def)
    hence "exec_meth (compP2 P) (compE2 e @ [AStore, Push Unit]) (stack_xlift (length [v2, v]) (compxE2 e 0 0)) h ([] @ [v2, v], loc, 0, None) ta h' (stk', loc', pc' - length (compE2 a @ compE2 i), xcp')"
      by(rule exec_meth_drop_xt) auto
    hence "exec_meth (compP2 P) (compE2 e) (stack_xlift (length [v2, v]) (compxE2 e 0 0)) h ([] @ [v2, v], loc, 0, None) ta h' (stk', loc', pc' - length (compE2 a @ compE2 i), xcp')"
      by(rule exec_meth_take) simp
    with bisim3 obtain stk'' where stk': "stk' = stk'' @ [v2, v]"
      and exec'': "exec_move P e h ([], loc, 0, None) ta h' (stk'', loc', pc' - length (compE2 a @ compE2 i), xcp')"
      unfolding exec_move_def by(blast dest: exec_meth_stk_split)
    from pc xcp have \<tau>: "\<tau>move2 (a\<lfloor>i\<rceil>:= e) (length (compE2 a) + length (compE2 i)) None = \<tau>move2 e 0 None"
      by(auto intro: \<tau>move2_AAssD3 dest: \<tau>move2AAss3)
    from bisim2 have "length xs = length loc" by(rule bisim1_length_xs)
    with IH3[OF exec'' _ wt3] len obtain e'' xs''
      where bisim': "P,e,n,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk'', loc', pc' - length (compE2 a) - length (compE2 i), xcp')"
      and red: "?red e loc e'' xs'' e 0 None" by auto
    from bisim' `bsok a n` `bsok i n`
    have "P,a\<lfloor>i\<rceil> := e,n,h' \<turnstile> (Val v\<lfloor>Val v2\<rceil> := e'', xs'') \<leftrightarrow> (stk'' @ [v2, v], loc', length (compE2 a) + length (compE2 i) + (pc' - length (compE2 a) - length (compE2 i)), xcp')"
      by(rule bisim1_bisims1.bisim1AAss3)
    moreover from red \<tau> have "?red (Val v\<lfloor>Val v2\<rceil> := e) loc (Val v\<lfloor>Val v2\<rceil> := e'') xs'' (a\<lfloor>i\<rceil> := e) (length (compE2 a) + length (compE2 i)) None"
      by(fastsimp intro: AAss1Red3)
    moreover from exec' have "pc' \<ge> length (compE2 a @ compE2 i)"
      by(rule exec_meth_drop_xt_pc) auto
    ultimately show ?thesis using \<tau> stk' pc xcp by(fastsimp elim!: \<tau>Red_trans intro: \<tau>Red_refl)
  qed
next
  case (bisim1AAss3 e n e' xs stk loc pc xcp a i v v')
  note IH3 = `\<And>stk' loc' pc' xcp' Env' T. 
             \<lbrakk> ?exec e stk loc pc xcp stk' loc' pc' xcp'; n + max_vars e' \<le> length xs; P,Env,h \<turnstile>1 e' : T \<rbrakk>
             \<Longrightarrow> \<exists>e'' xs''. P, e, n, h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp') \<and> ?red e' xs e'' xs'' e pc xcp`
  note exec = `?exec (a\<lfloor>i\<rceil> := e) (stk @ [v', v]) loc (length (compE2 a) + length (compE2 i) + pc) xcp stk' loc' pc' xcp'`
  note bisim3 = `P,e,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note len = `n + max_vars (Val v\<lfloor>Val v'\<rceil> := e') \<le> length xs`
  note wt = `P,Env,h \<turnstile>1 Val v\<lfloor>Val v'\<rceil> := e' : T`
  then obtain T3 where wt3: "P,Env,h \<turnstile>1 e' : T3" by auto
  from bisim3 have pc: "pc \<le> length (compE2 e)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e)")
    case True
    from exec have exec': "exec_meth (compP2 P) ((compE2 a @ compE2 i) @ compE2 e @ [AStore, Push Unit]) ((compxE2 a 0 0 @ compxE2 i (length (compE2 a)) (Suc 0)) @ shift (length (compE2 a @ compE2 i)) (stack_xlift (length [v', v]) (compxE2 e 0 0))) h (stk @ [v', v], loc, length (compE2 a @ compE2 i) + pc, xcp) ta h' (stk', loc', pc', xcp')"
      by(simp add: shift_compxE2 stack_xlift_compxE2 exec_move_def)
    hence "exec_meth (compP2 P) (compE2 e @ [AStore, Push Unit]) (stack_xlift (length [v', v]) (compxE2 e 0 0)) h (stk @ [v', v], loc, pc, xcp) ta h' (stk', loc', pc' - length (compE2 a @ compE2 i), xcp')"
      by(rule exec_meth_drop_xt) auto
    hence "exec_meth (compP2 P) (compE2 e) (stack_xlift (length [v', v]) (compxE2 e 0 0)) h (stk @ [v', v], loc, pc, xcp) ta h' (stk', loc', pc' - length (compE2 a @ compE2 i), xcp')"
      using True by(rule exec_meth_take)
    with bisim3 obtain stk'' where stk': "stk' = stk'' @ [v', v]"
      and exec'': "exec_move P e h (stk, loc, pc, xcp) ta h' (stk'', loc', pc' - length (compE2 a @ compE2 i), xcp')"
      unfolding exec_move_def by(blast dest: exec_meth_stk_split)
    from True have \<tau>: "\<tau>move2 (a\<lfloor>i\<rceil> := e) (length (compE2 a) + length (compE2 i) + pc) xcp = \<tau>move2 e pc xcp"
      by(auto intro: \<tau>move2AAss3)
    moreover from IH3[OF exec'' _ wt3] len obtain e'' xs''
      where bisim': "P,e,n,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk'', loc', pc' - length (compE2 a) - length (compE2 i), xcp')"
      and red: "?red e' xs e'' xs'' e pc xcp" by auto
    from bisim' `bsok a n` `bsok i n`
    have "P,a\<lfloor>i\<rceil> := e,n,h' \<turnstile> (Val v\<lfloor>Val v'\<rceil> := e'', xs'') \<leftrightarrow> (stk'' @ [v', v], loc', length (compE2 a) + length (compE2 i) + (pc' - length (compE2 a) - length (compE2 i)), xcp')"
      by(rule bisim1_bisims1.bisim1AAss3)
    moreover from exec' have "pc' \<ge> length (compE2 a @ compE2 i)"
      by(rule exec_meth_drop_xt_pc) auto
    ultimately show ?thesis using red \<tau> stk' True by(fastsimp intro: AAss1Red3)
  next
    case False
    with pc have [simp]: "pc = length (compE2 e)" by simp
    with bisim3 obtain v2 where stk: "stk = [v2]" and xcp: "xcp = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with bisim3 pc len have red: "\<tau>Red P h e' xs (Val v2) loc" by(auto intro: bisim1_Val_\<tau>Red)
    hence "\<tau>Red P h (Val v\<lfloor>Val v'\<rceil> := e') xs (Val v\<lfloor>Val v'\<rceil> := Val v2) loc" by auto
    moreover have \<tau>: "\<not> \<tau>move2 (a\<lfloor>i\<rceil> := e) (length (compE2 a) + length (compE2 i) + length (compE2 e)) None"
      by(fastsimp elim: \<tau>move2.cases dest: \<tau>move2_pc_length_compE2)
    moreover from `bsok a n` `bsok i n` `bsok e n` have B: "bsok (a\<lfloor>i\<rceil> := e) n" by(auto)
    have "\<exists>ta' e''. P,a\<lfloor>i\<rceil> := e,n,h' \<turnstile> (e'',loc) \<leftrightarrow> (stk', loc', pc', xcp') \<and> P \<turnstile>1 \<langle>Val v\<lfloor>Val v'\<rceil> := Val v2, (h, loc)\<rangle> -ta'\<rightarrow> \<langle>e'',(h', loc)\<rangle> \<and> ta_bisim (wbisim1 P) ta' ta"
    proof(cases "v = Null")
      case True with exec stk xcp `bsok a n` `bsok i n` `bsok e n` show ?thesis
	by(fastsimp elim!: exec_meth.cases simp add: exec_move_def intro: bisim1AAssNull Red1AAssNull)
    next
      case False
      with wt obtain U el A I where [simp]: "v = Addr A" "v' = Intg I"
	and hA: "h A = \<lfloor>Arr U el\<rfloor>" by fastsimp
      from bisim3 stk xcp wt3 have wt3': "P,Env,h \<turnstile>1 Val v2 : T3"
	by(auto dest: bisim1_length_compE2_WTrt_eq)
      show ?thesis
      proof(cases "0 \<le> I \<and> I < int (length el)")
	case True
	note I = True
	show ?thesis
	proof(cases "P \<turnstile> T3 \<le> U")
	  case True
	  with exec stk xcp True hA I wt3' `bsok a n` `bsok e n` `bsok i n` show ?thesis
	    by(fastsimp elim!: exec_meth.cases simp add: cast_ok_def compP2_def exec_move_def intro: Red1AAss bisim1AAss4)
	next
	  case False
	  with exec stk xcp True hA I wt3' `bsok a n` `bsok e n` `bsok i n` show ?thesis
	    by(fastsimp elim!: exec_meth.cases simp add: cast_ok_def compP2_def exec_move_def intro: Red1AAssStore bisim1AAssStore)
	qed
      next
	case False
	with exec stk xcp hA `bsok a n` `bsok i n` `bsok e n` show ?thesis
	  by(fastsimp elim!: exec_meth.cases intro: bisim1AAssBounds Red1AAssBounds simp add: exec_move_def)
      qed
    qed
    ultimately show ?thesis using exec xcp stk by fastsimp
  qed
next
  case (bisim1AAssThrow1 A n a xs stk loc pc i e)
  note exec = `?exec (A\<lfloor>i\<rceil> := e) stk loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  note bisim1 = `P,A,n,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)`
  from bisim1 have pc: "pc < length (compE2 A)" by(auto dest: bisim1_ThrowD)
  from bisim1 have "match_ex_table (compP2 P) (cname_of h a) (0 + pc) (compxE2 A 0 0) = None"
    unfolding compP2_def by(rule bisim1_xcp_Some_not_caught)
  with exec pc have False
    by(auto elim!: exec_meth.cases simp add: match_ex_table_not_pcs_None exec_move_def)
  thus ?case ..
next
  case (bisim1AAssThrow2 i n a xs stk loc pc A e v)
  note exec = `?exec (A\<lfloor>i\<rceil> := e) (stk @ [v]) loc (length (compE2 A) + pc) \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  note bisim2 = `P,i,n,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)`
  from bisim2 have pc: "pc < length (compE2 i)" by(auto dest: bisim1_ThrowD)
  from bisim2 have "match_ex_table (compP2 P) (cname_of h a) (length (compE2 A) + pc) (compxE2 i (length (compE2 A)) 0) = None"
    unfolding compP2_def by(rule bisim1_xcp_Some_not_caught)
  with exec pc have False
    apply(auto elim!: exec_meth.cases simp add: compxE2_stack_xlift_convs compxE2_size_convs exec_move_def)
    apply(auto simp add: match_ex_table_append_not_pcs)
    done
  thus ?case .. 
next
  case (bisim1AAssThrow3 e n a xs stk loc pc A i v' v)
  note exec = `?exec (A\<lfloor>i\<rceil> := e) (stk @ [v', v]) loc (length (compE2 A) + length (compE2 i) + pc) \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  note bisim2 = `P,e,n,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)`
  from bisim2 have "match_ex_table (compP2 P) (cname_of h a) (length (compE2 A) + length (compE2 i) + pc) (compxE2 e (length (compE2 A) + length (compE2 i)) 0) = None"
    unfolding compP2_def by(rule bisim1_xcp_Some_not_caught)
  with exec have False
    apply(auto elim!: exec_meth.cases simp add: compxE2_stack_xlift_convs compxE2_size_convs exec_move_def)
    apply(auto dest!: match_ex_table_stack_xliftD match_ex_table_shift_pcD dest: match_ex_table_pcsD simp add: match_ex_table_append match_ex_table_shift_pc_None)
    done
  thus ?case .. 
next
  case (bisim1AAssNull a n i e xs v' v)
  note exec = `?exec (a\<lfloor>i\<rceil> := e) [v', v, Null] xs (length (compE2 a) + length (compE2 i) + length (compE2 e)) \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor> stk' loc' pc' xcp'`
  hence False
    by(auto elim!: exec_meth.cases simp add: match_ex_table_append exec_move_def
            dest!: match_ex_table_shift_pcD match_ex_table_pc_length_compE2)
  thus ?case ..
next
  case (bisim1AAssBounds a n i e xs v' v A)
  note exec = `?exec (a\<lfloor>i\<rceil> := e) [v', v, Addr A] xs (length (compE2 a) + length (compE2 i) + length (compE2 e)) \<lfloor>addr_of_sys_xcpt ArrayIndexOutOfBounds\<rfloor> stk' loc' pc' xcp'`
  hence False
    by(auto elim!: exec_meth.cases simp add: match_ex_table_append exec_move_def
               dest!: match_ex_table_shift_pcD match_ex_table_pc_length_compE2)
  thus ?case ..
next
  case (bisim1AAssStore a n i e xs v' v A)
  note exec = `?exec (a\<lfloor>i\<rceil> := e) [v', v, Addr A] xs (length (compE2 a) + length (compE2 i) + length (compE2 e)) \<lfloor>addr_of_sys_xcpt ArrayStore\<rfloor> stk' loc' pc' xcp'`
  hence False
    by(auto elim!: exec_meth.cases simp add: match_ex_table_append exec_move_def
               dest!: match_ex_table_shift_pcD match_ex_table_pc_length_compE2)
  thus ?case ..
next
  case (bisim1AAss4 a n i e xs)
  from `bsok a n` `bsok i n` `bsok e n` have "bsok (a\<lfloor>i\<rceil> := e) n" by auto
  hence "P,a\<lfloor>i\<rceil> := e,n,h \<turnstile> (unit, xs) \<leftrightarrow> ([Unit], xs, length (compE2 (a\<lfloor>i\<rceil> := e)), None)" by(rule bisim1Val2)
  moreover have "\<tau>move2 (a\<lfloor>i\<rceil> := e) (Suc (length (compE2 a) + length (compE2 i) + length (compE2 e))) None"
    by(rule \<tau>move2AAssRed)
  moreover note `?exec (a\<lfloor>i\<rceil> := e) [] xs (Suc (length (compE2 a) + length (compE2 i) + length (compE2 e))) None stk' loc' pc' xcp'`
  ultimately show ?case
    by(fastsimp elim!: exec_meth.cases simp add: add_ac exec_move_def intro: \<tau>Red_refl)
next
  case (bisim1ALength a n a' xs stk loc pc xcp)
  note IH = `\<And>stk' loc' pc' xcp' Env' T. 
            \<lbrakk> ?exec a stk loc pc xcp stk' loc' pc' xcp'; n + max_vars a' \<le> length xs; P,Env,h \<turnstile>1 a' : T \<rbrakk>
            \<Longrightarrow> \<exists>e'' xs''. P, a, n, h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp') \<and> ?red a' xs e'' xs'' a pc xcp`
  note exec = `?exec (a\<bullet>length) stk loc pc xcp stk' loc' pc' xcp'`
  note bisim = `P,a,n,h \<turnstile> (a', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note len = `n + max_vars (a'\<bullet>length) \<le> length xs`
  from `P,Env,h \<turnstile>1 a'\<bullet>length : T` obtain T1 where wt1: "P,Env,h \<turnstile>1 a' : T1" by auto
  from bisim have pc: "pc \<le> length (compE2 a)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 a)")
    case True
    with exec have exec': "?exec a stk loc pc xcp stk' loc' pc' xcp'" by(auto simp add: exec_move_ALength)
    from True have \<tau>: "\<tau>move2 (a\<bullet>length) pc xcp = \<tau>move2 a pc xcp" by(auto intro: \<tau>move2ALength)
    with IH[OF exec' _ wt1] len obtain e'' xs''
      where bisim': "P,a,n,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp')"
      and red: "?red a' xs e'' xs'' a pc xcp" by auto
    from bisim' have "P,a\<bullet>length,n,h' \<turnstile> (e''\<bullet>length, xs'') \<leftrightarrow> (stk', loc', pc', xcp')"
      by(rule bisim1_bisims1.bisim1ALength)
    with red \<tau> show ?thesis by(fastsimp intro: ALength1Red)
  next
    case False
    with pc have pc: "pc = length (compE2 a)" by auto
    with bisim obtain v where stk: "stk = [v]" and xcp: "xcp = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with bisim pc len have "\<tau>Red P h a' xs (Val v) loc" by(auto intro: bisim1_Val_\<tau>Red)
    hence "\<tau>Red P h (a'\<bullet>length) xs (Val v\<bullet>length) loc" by auto
    moreover
    moreover have \<tau>: "\<not> \<tau>move2 (a\<bullet>length) (length (compE2 a)) None"
      by(fastsimp elim: \<tau>move2_cases dest: \<tau>move2_pc_length_compE2)
    moreover have "\<exists>ta' e''. P,a\<bullet>length,n,h' \<turnstile> (e'',loc) \<leftrightarrow> (stk', loc', pc', xcp') \<and> P \<turnstile>1 \<langle>Val v\<bullet>length, (h, loc)\<rangle> -ta'\<rightarrow> \<langle>e'',(h', loc)\<rangle> \<and> ta_bisim (wbisim1 P) ta' ta"
    proof(cases "v = Null")
      case True with exec stk xcp `bsok a n` pc show ?thesis
	by(fastsimp elim!: exec_meth.cases simp add: exec_move_def intro: bisim1ALengthNull Red1ALengthNull)
    next
      case False
      with bisim stk xcp pc `P,Env,h \<turnstile>1 a'\<bullet>length : T`
      obtain U el A where [simp]: "v = Addr A"
	and hA: "h A = \<lfloor>Arr U el\<rfloor>" by(fastsimp dest: bisim1_length_compE2_WTrt_eq)
      from `bsok a n` have "bsok (a\<bullet>length) n" by auto
      hence "P,a\<bullet>length,n,h' \<turnstile> (Val (Intg (int (length el))),loc) \<leftrightarrow> ([Intg (int (length el))], loc, length (compE2 (a\<bullet>length)), None)"
	by(rule bisim1Val2)
      thus ?thesis using exec stk xcp hA pc
	by(fastsimp elim!: exec_meth.cases intro: Red1ALength simp add: exec_move_def)
    qed
    ultimately show ?thesis using \<tau> pc xcp by(fastsimp elim!: \<tau>Red_trans intro: \<tau>Red_refl)
  qed
next
  case (bisim1ALengthThrow A n a xs stk loc pc)
  note exec = `?exec (A\<bullet>length) stk loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  note bisim1 = `P,A,n,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)`
  from bisim1 have pc: "pc < length (compE2 A)" by(auto dest: bisim1_ThrowD)
  from bisim1 have "match_ex_table (compP2 P) (cname_of h a) (0 + pc) (compxE2 A 0 0) = None"
    unfolding compP2_def by(rule bisim1_xcp_Some_not_caught)
  with exec pc have False by(auto elim!: exec_meth.cases simp add: exec_move_def)
  thus ?case ..
next
  case (bisim1ALengthNull a n xs)
  note exec = `?exec (a\<bullet>length) [Null] xs (length (compE2 a)) \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor> stk' loc' pc' xcp'`
  hence False by(auto elim!: exec_meth.cases dest!: match_ex_table_pc_length_compE2 simp add: exec_move_def)
  thus ?case ..
next
  case (bisim1FAcc e n e' xs stk loc pc xcp F D)
  note IH = `\<And>stk' loc' pc' xcp' Env' T. 
            \<lbrakk> ?exec e stk loc pc xcp stk' loc' pc' xcp'; n + max_vars e' \<le> length xs; P,Env,h \<turnstile>1 e' : T \<rbrakk>
            \<Longrightarrow> \<exists>e'' xs''. P, e, n, h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp') \<and> ?red e' xs e'' xs'' e pc xcp`
  note exec = `?exec (e\<bullet>F{D}) stk loc pc xcp stk' loc' pc' xcp'`
  note bisim = `P,e,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note len = `n + max_vars (e'\<bullet>F{D}) \<le> length xs`
  from `P,Env,h \<turnstile>1 e'\<bullet>F{D} : T` obtain T1 where wt1: "P,Env,h \<turnstile>1 e' : T1" by auto
  from bisim have pc: "pc \<le> length (compE2 e)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e)")
    case True
    with exec have exec': "?exec e stk loc pc xcp stk' loc' pc' xcp'" by(simp add: exec_move_FAcc)
    from True have \<tau>: "\<tau>move2 (e\<bullet>F{D}) pc xcp = \<tau>move2 e pc xcp" by(auto intro: \<tau>move2FAcc)
    with IH[OF exec' _ wt1] len obtain e'' xs''
      where bisim': "P,e,n,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp')"
      and red: "?red e' xs e'' xs'' e pc xcp" by auto
    from bisim' have "P,e\<bullet>F{D},n,h' \<turnstile> (e''\<bullet>F{D}, xs'') \<leftrightarrow> (stk', loc', pc', xcp')"
      by(rule bisim1_bisims1.bisim1FAcc)
    with red \<tau> show ?thesis by(fastsimp intro: FAcc1Red)
  next
    case False
    with pc have pc: "pc = length (compE2 e)" by auto
    with bisim obtain v where stk: "stk = [v]" and xcp: "xcp = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with bisim pc len have "\<tau>Red P h e' xs (Val v) loc" by(auto intro: bisim1_Val_\<tau>Red)
    hence "\<tau>Red P h (e'\<bullet>F{D}) xs (Val v\<bullet>F{D}) loc" by auto
    moreover have \<tau>: "\<not> \<tau>move2 (e\<bullet>F{D}) (length (compE2 e)) None"
      by(fastsimp elim: \<tau>move2_cases dest: \<tau>move2_pc_length_compE2)
    moreover have "\<exists>ta' e''. P,e\<bullet>F{D},n,h' \<turnstile> (e'',loc) \<leftrightarrow> (stk', loc', pc', xcp') \<and> P \<turnstile>1 \<langle>Val v\<bullet>F{D}, (h, loc)\<rangle> -ta'\<rightarrow> \<langle>e'',(h', loc)\<rangle> \<and> ta_bisim (wbisim1 P) ta' ta"
    proof(cases "v = Null")
      case True with exec stk xcp `bsok e n` pc show ?thesis
	by(fastsimp elim!: exec_meth.cases simp add: exec_move_def intro: bisim1FAccNull Red1FAccNull)
    next
      case False
      with bisim stk xcp pc `P,Env,h \<turnstile>1 e'\<bullet>F{D} : T`
      obtain A C fs where [simp]: "v = Addr A"
	and hA: "h A = \<lfloor>Obj C fs\<rfloor>" and fs: "P \<turnstile> C has F:T in D" by(fastsimp dest: bisim1_length_compE2_WTrt_eq)
      from hA hconf fs obtain v' where v': "fs (F, D) = \<lfloor>v'\<rfloor>" by(fastsimp dest!: hconfD simp add: oconf_def)
      from `bsok e n` have "bsok (e\<bullet>F{D}) n" by auto
      hence "P,e\<bullet>F{D},n,h' \<turnstile> (Val v',loc) \<leftrightarrow> ([v'], loc, length (compE2 (e\<bullet>F{D})), None)"
	by(rule bisim1Val2)
      thus ?thesis using exec stk xcp hA pc fs v'
	by(fastsimp elim!: exec_meth.cases intro: Red1FAcc simp add: exec_move_def)
    qed
    ultimately show ?thesis using \<tau> pc xcp by(fastsimp elim!: \<tau>Red_trans intro: \<tau>Red_refl)
  qed
next
  case (bisim1FAccThrow e n a xs stk loc pc F D)
  note exec = `?exec (e\<bullet>F{D}) stk loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  note bisim1 = `P,e,n,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)`
  from bisim1 have pc: "pc < length (compE2 e)" by(auto dest: bisim1_ThrowD)
  from bisim1 have "match_ex_table (compP2 P) (cname_of h a) (0 + pc) (compxE2 e 0 0) = None"
    unfolding compP2_def by(rule bisim1_xcp_Some_not_caught)
  with exec pc have False by(auto elim!: exec_meth.cases simp add: exec_move_def)
  thus ?case ..
next
  case (bisim1FAccNull e n F D xs)
  note exec = `?exec (e\<bullet>F{D}) [Null] xs (length (compE2 e)) \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor> stk' loc' pc' xcp'`
  hence False by(auto elim!: exec_meth.cases dest!: match_ex_table_pc_length_compE2 simp add: exec_move_def)
  thus ?case ..
next
  case (bisim1FAss1 e n e' xs stk loc pc xcp e2 F D)
  note IH1 = `\<And>stk' loc' pc' xcp' Env' T. 
             \<lbrakk> ?exec e stk loc pc xcp stk' loc' pc' xcp'; n + max_vars e' \<le> length xs; P,Env,h \<turnstile>1 e' : T \<rbrakk>
             \<Longrightarrow> \<exists>e'' xs''. P, e, n, h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp') \<and> ?red e' xs e'' xs'' e pc xcp`
  note IH2 = `\<And>xs stk' loc' pc' xcp' Env' T. 
             \<lbrakk> ?exec e2 [] xs 0 None stk' loc' pc' xcp'; n + max_vars e2 \<le> length xs; P,Env,h \<turnstile>1 e2 : T \<rbrakk>
             \<Longrightarrow> \<exists>e'' xs''. P, e2, n, h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp') \<and> ?red e2 xs e'' xs'' e2 0 None`
  note exec = `?exec (e\<bullet>F{D} := e2) stk loc pc xcp stk' loc' pc' xcp'`
  note bisim1 = `P,e,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim2 = `P,e2,n,h \<turnstile> (e2, loc) \<leftrightarrow> ([], loc, 0, None)`
  note len = `n + max_vars (e'\<bullet>F{D} := e2) \<le> length xs`
  from `P,Env,h \<turnstile>1 e'\<bullet>F{D} := e2 : T` obtain T1 T2
    where wt1: "P,Env,h \<turnstile>1 e' : T1" and wt2: "P,Env,h \<turnstile>1 e2 : T2" by auto
  from bisim1 have pc: "pc \<le> length (compE2 e)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e)")
    case True
    with exec have exec': "?exec e stk loc pc xcp stk' loc' pc' xcp'" by(simp add: exec_move_FAss1)
    from True have \<tau>: "\<tau>move2 (e\<bullet>F{D} := e2) pc xcp = \<tau>move2 e pc xcp" by(auto intro: \<tau>move2FAss1)
    with IH1[OF exec' _ wt1] len obtain e'' xs''
      where bisim': "P,e,n,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp')"
      and red: "?red e' xs e'' xs'' e pc xcp" by auto
    from bisim' `bsok e2 n` have "P,e\<bullet>F{D} := e2,n,h' \<turnstile> (e''\<bullet>F{D} := e2, xs'') \<leftrightarrow> (stk', loc', pc', xcp')"
      by(rule bisim1_bisims1.bisim1FAss1)
    with red \<tau> show ?thesis by(fastsimp intro: FAss1Red1)
  next
    case False
    with pc have pc: "pc = length (compE2 e)" by auto
    with bisim1 obtain v where stk: "stk = [v]" and xcp: "xcp = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with bisim1 pc len have rede1': "\<tau>Red P h e' xs (Val v) loc" by(auto intro: bisim1_Val_\<tau>Red)
    hence "\<tau>Red P h (e'\<bullet>F{D} := e2) xs (Val v\<bullet>F{D} := e2) loc" by auto
    moreover from pc exec stk xcp
    have exec': "exec_meth (compP2 P) (compE2 e @ compE2 e2 @ [Putfield F D, Push Unit]) (compxE2 e 0 0 @ shift (length (compE2 e)) (stack_xlift (length [v]) (compxE2 e2 0 0))) h ([] @ [v], loc, length (compE2 e) + 0, None) ta h' (stk', loc', pc', xcp')"
      by(simp add: compxE2_size_convs compxE2_stack_xlift_convs exec_move_def)
    hence "exec_meth (compP2 P) (compE2 e2 @ [Putfield F D, Push Unit]) (stack_xlift (length [v]) (compxE2 e2 0 0)) h ([] @ [v], loc, 0, None) ta h' (stk', loc', pc' - length (compE2 e), xcp')"
      by(rule exec_meth_drop_xt) auto
    hence "exec_meth (compP2 P) (compE2 e2) (stack_xlift (length [v]) (compxE2 e2 0 0)) h ([] @ [v], loc, 0, None) ta h' (stk', loc', pc' - length (compE2 e), xcp')"
      by(rule exec_meth_take) simp
    with bisim2 obtain stk'' where stk': "stk' = stk'' @ [v]"
      and exec'': "exec_move P e2 h ([], loc, 0, None) ta h' (stk'', loc', pc' - length (compE2 e), xcp')"
      unfolding exec_move_def by(blast dest: exec_meth_stk_split)
    from pc xcp have \<tau>: "\<tau>move2 (e\<bullet>F{D} := e2) (length (compE2 e)) None = \<tau>move2 e2 0 None"
      by(auto intro: \<tau>move2_FAssD2 dest: \<tau>move2FAss2)
    from bisim1 have "length xs = length loc" by(rule bisim1_length_xs)
    with IH2[OF exec'' _ wt2] len obtain e'' xs''
      where bisim': "P,e2,n,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk'', loc', pc' - length (compE2 e), xcp')"
      and red: "?red e2 loc e'' xs'' e2 0 None" by auto
    from bisim' `bsok e n`
    have "P,e\<bullet>F{D} := e2,n,h' \<turnstile> (Val v\<bullet>F{D} := e'', xs'') \<leftrightarrow> (stk'' @ [v], loc', length (compE2 e) + (pc' - length (compE2 e)), xcp')"
      by(rule bisim1_bisims1.bisim1FAss2)
    moreover from red \<tau> have "?red (Val v\<bullet>F{D} := e2) loc (Val v\<bullet>F{D} := e'') xs'' (e\<bullet>F{D} := e2) (length (compE2 e)) None"
      by(fastsimp intro: FAss1Red2)
    moreover from exec' have "pc' \<ge> length (compE2 e)"
      by(rule exec_meth_drop_xt_pc) auto
    ultimately show ?thesis using \<tau> stk' pc xcp by(fastsimp elim!: \<tau>Red_trans intro: \<tau>Red_refl)
  qed
next
  case (bisim1FAss2 e2 n e' xs stk loc pc xcp e F D v)
  note IH2 = `\<And>stk' loc' pc' xcp' Env' T. 
             \<lbrakk> ?exec e2 stk loc pc xcp stk' loc' pc' xcp'; n + max_vars e' \<le> length xs; P,Env,h \<turnstile>1 e' : T \<rbrakk>
             \<Longrightarrow> \<exists>e'' xs''. P, e2, n, h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp') \<and> ?red e' xs e'' xs'' e2 pc xcp`
  note exec = `?exec (e\<bullet>F{D} := e2) (stk @ [v]) loc (length (compE2 e) + pc) xcp stk' loc' pc' xcp'`
  note bisim2 = `P,e2,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note len = `n + max_vars (Val v\<bullet>F{D} := e') \<le> length xs`
  note wt = `P,Env,h \<turnstile>1 Val v\<bullet>F{D} := e' : T`
  then obtain T' where wt1: "P,Env,h \<turnstile>1 e' : T'" by auto
  from bisim2 have pc: "pc \<le> length (compE2 e2)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e2)")
    case True
    from exec have exec': "exec_meth (compP2 P) (compE2 e @ compE2 e2 @ [Putfield F D, Push Unit]) (compxE2 e 0 0 @ shift (length (compE2 e)) (stack_xlift (length [v]) (compxE2 e2 0 0))) h (stk @ [v], loc, length (compE2 e) + pc, xcp) ta h' (stk', loc', pc', xcp')"
      by(simp add: shift_compxE2 stack_xlift_compxE2 exec_move_def)
    hence "exec_meth (compP2 P) (compE2 e2 @ [Putfield F D, Push Unit]) (stack_xlift (length [v]) (compxE2 e2 0 0)) h (stk @ [v], loc, pc, xcp) ta h' (stk', loc', pc' - length (compE2 e), xcp')"
      by(rule exec_meth_drop_xt) auto
    hence "exec_meth (compP2 P) (compE2 e2) (stack_xlift (length [v]) (compxE2 e2 0 0)) h (stk @ [v], loc, pc, xcp) ta h' (stk', loc', pc' - length (compE2 e), xcp')"
      using True by(rule exec_meth_take)
    with bisim2 obtain stk'' where stk': "stk' = stk'' @ [v]"
      and exec'': "exec_move P e2 h (stk, loc, pc, xcp) ta h' (stk'', loc', pc' - length (compE2 e), xcp')"
      unfolding exec_move_def by(blast dest: exec_meth_stk_split)
    from True have \<tau>: "\<tau>move2 (e\<bullet>F{D} := e2) (length (compE2 e) + pc) xcp = \<tau>move2 e2 pc xcp"
      by(auto intro: \<tau>move2FAss2)
    moreover from IH2[OF exec'' _ wt1] len obtain e'' xs''
      where bisim': "P,e2,n,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk'', loc', pc' - length (compE2 e), xcp')"
      and red: "?red e' xs e'' xs'' e2 pc xcp" by auto
    from bisim' `bsok e n` have "P,e\<bullet>F{D} := e2,n,h' \<turnstile> (Val v\<bullet>F{D} := e'', xs'') \<leftrightarrow> (stk'' @ [v], loc', length (compE2 e) + (pc' - length (compE2 e)), xcp')"
      by(rule bisim1_bisims1.bisim1FAss2)
    moreover from exec' have "pc' \<ge> length (compE2 e)"
      by(rule exec_meth_drop_xt_pc) auto
    ultimately show ?thesis using red \<tau> stk' True by(fastsimp intro: FAss1Red2)
  next
    case False
    with pc have [simp]: "pc = length (compE2 e2)" by simp
    with bisim2 obtain v2 where stk: "stk = [v2]" and xcp: "xcp = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with bisim2 pc len have red: "\<tau>Red P h e' xs (Val v2) loc" by(auto intro: bisim1_Val_\<tau>Red)
    hence "\<tau>Red P h (Val v\<bullet>F{D} := e') xs (Val v\<bullet>F{D} := Val v2) loc" by auto
    moreover have \<tau>: "\<not> \<tau>move2 (e\<bullet>F{D} := e2) (length (compE2 e) + length (compE2 e2)) None"
      by(fastsimp elim: \<tau>move2.cases dest: \<tau>move2_pc_length_compE2)
    moreover from `bsok e n` `bsok e2 n` have B: "bsok (e\<bullet>F{D} := e2) n" by(auto)
    have "\<exists>ta' e''. P,e\<bullet>F{D} := e2,n,h' \<turnstile> (e'',loc) \<leftrightarrow> (stk', loc', pc', xcp') \<and> P \<turnstile>1 \<langle>Val v\<bullet>F{D} := Val v2, (h, loc)\<rangle> -ta'\<rightarrow> \<langle>e'',(h', loc)\<rangle> \<and> ta_bisim (wbisim1 P) ta' ta"
    proof(cases "v = Null")
      case True with exec stk xcp `bsok e n` `bsok e2 n` show ?thesis
	by(fastsimp elim!: exec_meth.cases simp add: exec_move_def intro: bisim1FAssNull Red1FAssNull)
    next
      case False with exec stk xcp `bsok e n` `bsok e2 n` wt show ?thesis
	by(force elim!: exec_meth.cases simp add: compP2_def exec_move_def intro: bisim1FAss3 Red1FAss)
    qed
    ultimately show ?thesis using exec xcp stk by fastsimp
  qed
next
  case (bisim1FAssThrow1 e n a xs stk loc pc e2 F D)
  note exec = `?exec (e\<bullet>F{D} := e2) stk loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  note bisim1 = `P,e,n,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)`
  from bisim1 have pc: "pc < length (compE2 e)" by(auto dest: bisim1_ThrowD)
  from bisim1 have "match_ex_table (compP2 P) (cname_of h a) (0 + pc) (compxE2 e 0 0) = None"
    unfolding compP2_def by(rule bisim1_xcp_Some_not_caught)
  with exec pc have False
    by(auto elim!: exec_meth.cases simp add: exec_move_def match_ex_table_not_pcs_None)
  thus ?case ..
next
  case (bisim1FAssThrow2 e2 n a xs stk loc pc e F D v)
  note exec = `?exec (e\<bullet>F{D} := e2) (stk @ [v]) loc (length (compE2 e) + pc) \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  note bisim2 = `P,e2,n,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)`
  hence "match_ex_table (compP2 P) (cname_of h a) (length (compE2 e) + pc) (compxE2 e2 (length (compE2 e)) 0) = None"
    unfolding compP2_def by(rule bisim1_xcp_Some_not_caught)
  with exec have False
    by(auto elim!: exec_meth.cases simp add: compxE2_stack_xlift_convs exec_move_def)(auto dest!: match_ex_table_stack_xliftD simp add: match_ex_table_append_not_pcs)
  thus ?case ..
next
  case (bisim1FAssNull e n e2 F D xs v)
  note exec = `?exec (e\<bullet>F{D} := e2) [v, Null] xs (length (compE2 e) + length (compE2 e2)) \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor> stk' loc' pc' xcp'`
  hence False
    by(auto elim!: exec_meth.cases simp add: match_ex_table_append_not_pcs compxE2_size_convs exec_move_def
               dest!: match_ex_table_shift_pcD match_ex_table_pc_length_compE2)
  thus ?case ..
next
  case (bisim1FAss3 e n e2 F D xs)
  from `bsok e n` `bsok e2 n` have "bsok (e\<bullet>F{D} := e2) n" by auto
  hence "P,e\<bullet>F{D} := e2,n,h \<turnstile> (unit, xs) \<leftrightarrow> ([Unit], xs, length (compE2 (e\<bullet>F{D} := e2)), None)" by(rule bisim1Val2)
  moreover have "\<tau>move2 (e\<bullet>F{D} := e2) (Suc (length (compE2 e) + length (compE2 e2))) None"
    by(rule \<tau>move2FAssRed)
  moreover note `?exec (e\<bullet>F{D} := e2) [] xs (Suc (length (compE2 e) + length (compE2 e2))) None stk' loc' pc' xcp'`
  ultimately show ?case
    by(fastsimp elim!: exec_meth.cases simp add: add_ac exec_move_def intro: \<tau>Red_refl)
next
  case (bisim1Call1 obj n obj' xs stk loc pc xcp ps M')
  note IH1 = `\<And>stk' loc' pc' xcp' Env' T. 
             \<lbrakk> ?exec obj stk loc pc xcp stk' loc' pc' xcp'; n + max_vars obj' \<le> length xs; P,Env,h \<turnstile>1 obj' : T \<rbrakk>
             \<Longrightarrow> \<exists>e'' xs''. P, obj, n, h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp') \<and> ?red obj' xs e'' xs'' obj pc xcp`
  note IH2 = `\<And>xs stk' loc' pc' xcp' Env' Ts. 
             \<lbrakk> ?execs ps [] xs 0 None stk' loc' pc' xcp'; n + max_varss ps \<le> length xs; P,Env,h \<turnstile>1 ps [:] Ts \<rbrakk>
             \<Longrightarrow> \<exists>es'' xs''. P, ps, n, h' \<turnstile> (es'', xs'') [\<leftrightarrow>] (stk', loc', pc', xcp') \<and> ?reds ps xs es'' xs'' ps 0 None`
  note exec = `?exec (obj\<bullet>M'(ps)) stk loc pc xcp stk' loc' pc' xcp'`
  note bisim1 = `P,obj,n,h \<turnstile> (obj', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim2 = `P,ps,n,h \<turnstile> (ps, loc) [\<leftrightarrow>] ([], loc, 0, None)`
  note len = `n + max_vars (obj'\<bullet>M'(ps)) \<le> length xs`
  note wt = `P,Env,h \<turnstile>1 obj'\<bullet>M'(ps) : T`
  then obtain Tobj Ts where wt1: "P,Env,h \<turnstile>1 obj' : Tobj" 
    and wt2: "P,Env,h \<turnstile>1 ps [:] Ts" by auto
  from bisim1 have pc: "pc \<le> length (compE2 obj)" by(rule bisim1_pc_length_compE2)
  from bisim1 have lenxs: "length xs = length loc" by(rule bisim1_length_xs)
  show ?case
  proof(cases "pc < length (compE2 obj)")
    case True
    with exec have exec': "?exec obj stk loc pc xcp stk' loc' pc' xcp'" by(simp add: exec_move_Call1)
    from True have "\<tau>move2 (obj\<bullet>M'(ps)) pc xcp = \<tau>move2 obj pc xcp" by(auto intro: \<tau>move2CallObj)
    with IH1[OF exec' _ wt1] bisim2 len show ?thesis
      by(fastsimp intro: bisim1_bisims1.bisim1Call1 bisims1_bsoks Call1Obj)
  next
    case False
    with pc have pc: "pc = length (compE2 obj)" by auto
    with bisim1 obtain v where stk: "stk = [v]" and xcp: "xcp = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with bisim1 pc len have "\<tau>Red P h obj' xs (Val v) loc" by(auto intro: bisim1_Val_\<tau>Red)
    hence red: "\<tau>Red P h (obj'\<bullet>M'(ps)) xs (Val v\<bullet>M'(ps)) loc" by auto
    show ?thesis
    proof(cases ps)
      case (Cons p ps')
      from pc exec stk xcp
      have "exec_meth (compP2 P) (compE2 (obj\<bullet>M'(ps))) (compxE2 (obj\<bullet>M'(ps)) 0 0) h ([] @ [v], loc, length (compE2 obj) + 0, None) ta h' (stk', loc', pc', xcp')"
	by(simp add: compxE2_size_convs compxE2_stack_xlift_convs exec_move_def)
      hence exec': "exec_meth (compP2 P) (compEs2 ps) (stack_xlift (length [v]) (compxEs2 ps 0 0)) h ([] @ [v], loc, 0, None) ta h' (stk', loc', pc' - length (compE2 obj), xcp')"
	and pc': "pc' \<ge> length (compE2 obj)" using Cons
	by(safe dest!: Call_execParamD) simp_all
      from exec' bisim2 obtain stk'' where stk': "stk' = stk'' @ [v]"
	and exec'': "exec_moves P ps h ([], loc, 0, None) ta h' (stk'', loc', pc' - length (compE2 obj), xcp')"
	unfolding exec_moves_def by -(drule (1) exec_meth_stk_splits, auto)
      from pc xcp have \<tau>: "\<tau>move2 (obj\<bullet>M'(ps)) (length (compE2 obj)) None = \<tau>moves2 ps 0 None"
	by(auto dest: \<tau>move2CallParams \<tau>move2_pc_length_compE2 elim: \<tau>move2.cases)
      from IH2[OF exec'' _ wt2] len lenxs obtain es'' xs''
	where bisim': "P,ps,n,h' \<turnstile> (es'', xs'') [\<leftrightarrow>] (stk'', loc', pc' - length (compE2 obj), xcp')"
	and red': "?reds ps loc es'' xs'' ps 0 None" by auto
      from bisim' bisim1 have "P,obj\<bullet>M'(ps),n,h' \<turnstile> (Val v\<bullet>M'(es''), xs'') \<leftrightarrow> (stk'' @ [v], loc', length (compE2 obj) + (pc' - length (compE2 obj)), xcp')"
	by(rule bisim1CallParams[OF _ bisim1_bsok])
      thus ?thesis using red red' \<tau> stk' pc xcp pc' by(fastsimp elim!: \<tau>Red_trans intro: Call1Params)
    next
      case Nil[simp]
      have \<tau>: "\<not> \<tau>move1 (Val v\<bullet>M'([]))" "\<not> \<tau>move2 (obj\<bullet>M'(ps)) (length (compE2 obj)) None"
	by(auto elim: \<tau>move2_cases \<tau>moves2.cases dest: \<tau>move2_pc_length_compE2)
      from bisim1 stk xcp pc have wtobj'D: "\<And>T. P,Env,h \<turnstile>1 obj' : T \<Longrightarrow> P,Env,h \<turnstile>1 Val v : T"
	by(auto dest: bisim1_length_compE2_WTrt_eq)
      with exec pc wt stk xcp
      have "v = Null \<or> (is_Addr v \<and> (\<exists>T. typeof\<^bsub>h\<^esub> v = \<lfloor>T\<rfloor> \<and> is_external_call P T M' 0))" (is "_ \<or> ?rest")
	by(auto elim!: exec_meth.cases is_ArrE simp add: is_Ref_def exec_move_def compP2_def split: heapobj.split split_if_asm)
      thus ?thesis
      proof
	assume [simp]: "v = Null"
	from bisim1 have "P,obj\<bullet>M'([]),n,h \<turnstile> (THROW NullPointer, loc) \<leftrightarrow> ([] @ [Null], loc, length (compE2 obj) + length (compEs2 []), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
	  by(safe intro!: bisim1CallThrow elim!: bisim1_bsok) simp_all
	moreover have "P \<turnstile>1 \<langle>null\<bullet>M'(map Val []),(h, loc)\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer,(h, loc)\<rangle>"
	  by(rule Red1CallNull)
	ultimately show ?thesis using exec pc stk xcp \<tau> red
	  by(fastsimp elim!: exec_meth.cases intro: \<tau>Red_trans simp add: exec_move_def)
      next
	assume ?rest
	then obtain a Ta where [simp]: "v = Addr a"
	  and Ta: "typeof\<^bsub>h\<^esub> (Addr a) = \<lfloor>Ta\<rfloor>"
	  and iec: "is_external_call P Ta M' 0" by auto
	with exec pc wt stk xcp wtobj'D
	obtain ta' va h'' U where redex: "(ta', va, h'') \<in> set (red_external_list (compP2 P) a M' [] h)"
	  and ret: "(xcp', h', [(stk', loc', arbitrary, arbitrary, pc')]) = extRet2JVM 0 h'' [Addr a] loc arbitrary arbitrary (length (compE2 obj)) [] va"
	  and wtext: "P \<turnstile> Ta\<bullet>M'([]) :: U"
	  and ta': "ta = extTA2JVM (compP2 P) ta'"
	  by(fastsimp elim!: exec_meth.cases is_ArrE simp add: is_Ref_def exec_move_def compP2_def has_method_def dest: sees_method_compPD external_call_not_sees_method[OF wf])
	from ret have [simp]: "h'' = h'" by simp
	from redex have redex': "P \<turnstile> \<langle>a\<bullet>M'([]), h\<rangle> -ta'\<rightarrow>ext \<langle>va, h'\<rangle>"
	  unfolding red_external_list_conv[symmetric] by(simp add: compP2_def)
	with Ta iec have "P \<turnstile>1 \<langle>addr a\<bullet>M'(map Val []), (h, loc)\<rangle> -extTA2J1 P ta'\<rightarrow> \<langle>extRet2J va, (h', loc)\<rangle>"
	  by -(rule Red1CallExternal, auto)
	moreover have "P,obj\<bullet>M'(ps),n,h' \<turnstile> (extRet2J va, loc) \<leftrightarrow> (stk', loc', pc', xcp')"
	proof(cases va)
	  case (Inl v)
	  have "P,obj\<bullet>M'([]),n,h' \<turnstile> (Val v, loc) \<leftrightarrow> ([v], loc, length (compE2 (obj\<bullet>M'([]))), None)"
	    by(rule bisim1Val2)(simp add: `bsok obj n`)
	  with ret Inl show ?thesis by simp
	next
	  case (Inr ad)
	  have "P,obj\<bullet>M'([]),n,h' \<turnstile> (Throw ad, loc) \<leftrightarrow> ([] @ [v], loc, length (compE2 (obj)) + length (compEs2 []), \<lfloor>ad\<rfloor>)"
	    by(rule bisim1CallThrow)(simp_all add: `bsok obj n`)
	  with ret Inr show ?thesis by simp
	qed
	moreover from Ta have "h a \<noteq> None" by auto
	with ta' redex' external_call_hconf[OF redex' Ta _ wtext hconf]
	have "ta_bisim (wbisim1 P) (extTA2J1 P ta') ta" by(auto intro: red_external_ta_bisim21[OF wf])
	ultimately show ?thesis using red \<tau> pc xcp by(fastsimp simp del: split_paired_Ex)
      qed
    qed
  qed
next
  case (bisim1CallParams ps n ps' xs stk loc pc xcp obj M' v)
  note bisim2 = `P,ps,n,h \<turnstile> (ps', xs) [\<leftrightarrow>] (stk, loc, pc, xcp)`
  note bisim1 = `P,obj,n,h \<turnstile> (obj, xs) \<leftrightarrow> ([], xs, 0, None)`
  note IH2 = `\<And>stk' loc' pc' xcp' Env' Ts. 
             \<lbrakk> ?execs ps stk loc pc xcp stk' loc' pc' xcp'; n + max_varss ps' \<le> length xs; P,Env,h \<turnstile>1 ps' [:] Ts \<rbrakk>
             \<Longrightarrow> \<exists>es'' xs''. P, ps, n, h' \<turnstile> (es'', xs'') [\<leftrightarrow>] (stk', loc', pc', xcp') \<and> ?reds ps' xs es'' xs'' ps pc xcp`
  note exec = `exec_move P (obj\<bullet>M'(ps)) h (stk @ [v], loc, length (compE2 obj) + pc, xcp) ta h' (stk', loc', pc', xcp')`
  note len = `n + max_vars (Val v\<bullet>M'(ps')) \<le> length xs`
  note wt = `P,Env,h \<turnstile>1 Val v\<bullet>M'(ps') : T`
  then obtain To Ts where wt1: "P,Env,h \<turnstile>1 Val v : To" and wt2: "P,Env,h \<turnstile>1 ps' [:] Ts" by auto
  from bisim2 have pc: "pc \<le> length (compEs2 ps)" by(rule bisims1_pc_length_compEs2)
  show ?case
  proof(cases "pc < length (compEs2 ps)")
    case True
    from exec have "exec_meth (compP2 P) (compE2 (obj\<bullet>M'(ps))) (compxE2 (obj\<bullet>M'(ps)) 0 0) h (stk @ [v], loc, length (compE2 obj) + pc, xcp) ta h' (stk', loc', pc', xcp')"
      by(simp add: exec_move_def)
    with True have exec': "exec_meth (compP2 P) (compEs2 ps) (stack_xlift (length [v]) (compxEs2 ps 0 0)) h (stk @ [v], loc, pc, xcp) ta h' (stk', loc', pc' - length (compE2 obj), xcp')"
      and pc': "pc' \<ge> length (compE2 obj)" by(safe dest!: Call_execParamD)
    from exec' bisim2 obtain stk'' where stk': "stk' = stk'' @ [v]"
      and exec'': "exec_moves P ps h (stk, loc, pc, xcp) ta h' (stk'', loc', pc' - length (compE2 obj), xcp')"
      by(unfold exec_moves_def)(drule (1) exec_meth_stk_splits, auto)
    from True have \<tau>: "\<tau>move2 (obj\<bullet>M'(ps)) (length (compE2 obj) + pc) xcp = \<tau>moves2 ps pc xcp"
      by(auto intro: \<tau>move2CallParams \<tau>moves2xcp dest: \<tau>move2_pc_length_compE2 elim: \<tau>move2.cases)
    from IH2[OF exec'' _ wt2] len obtain es'' xs''
      where bisim': "P,ps,n,h' \<turnstile> (es'', xs'') [\<leftrightarrow>] (stk'', loc', pc' - length (compE2 obj), xcp')"
      and red': "?reds ps' xs es'' xs'' ps pc xcp" by auto
    from bisim' bisim1 have "P,obj\<bullet>M'(ps),n,h' \<turnstile> (Val v\<bullet>M'(es''), xs'') \<leftrightarrow> (stk'' @ [v], loc', length (compE2 obj) + (pc' - length (compE2 obj)), xcp')"
      by(rule bisim1_bisims1.bisim1CallParams[OF _ bisim1_bsok])
    thus ?thesis using red' \<tau> stk' pc pc'
      by(fastsimp intro: Call1Params)
  next
    case False
    with pc have [simp]: "pc = length (compEs2 ps)" by simp
    with bisim2 obtain vs where [simp]: "stk = rev vs" "xcp = None"
      and lenvs: "length vs = length ps"
      by(auto dest: bisims1_pc_length_compEs2D)
    with bisim2 len have reds: "\<tau>Reds P h ps' xs (map Val vs) loc"
      by(auto intro: bisims1_Val_\<tau>Reds)
    have \<tau>: "\<not> \<tau>move1 (Val v\<bullet>M'(map Val vs))"
      "\<not> \<tau>move2 (obj\<bullet>M'(ps)) (length (compE2 obj) + length (compEs2 ps)) None"
    proof
      assume "\<tau>move1 (Val v\<bullet>M'(map Val vs))"
      thus False
      by(rule \<tau>move1_cases)(auto, induct vs, auto simp add: Cons_eq_append_conv)
    next
      show "\<not> \<tau>move2 (obj\<bullet>M'(ps)) (length (compE2 obj) + length (compEs2 ps)) None"
	by(fastsimp elim: \<tau>move2.cases dest: \<tau>move2_pc_length_compE2 \<tau>moves2_pc_length_compEs2)
    qed
    from exec wt lenvs 
    have "v = Null \<or> (is_Addr v \<and> (\<exists>T. typeof\<^bsub>h\<^esub> v = \<lfloor>T\<rfloor> \<and> is_external_call P T M' (length vs)))" (is "_ \<or> ?rest")
      by(auto elim!: exec_meth.cases is_ArrE simp add: is_Ref_def exec_move_def compP2_def split: heapobj.split split_if_asm)
    thus ?thesis
    proof
      assume [simp]: "v = Null"
      from bisim1 lenvs bisim2
      have "P,obj\<bullet>M'(ps),n,h \<turnstile> (THROW NullPointer, loc) \<leftrightarrow> (rev vs @ [Null], loc, length (compE2 obj) + length (compEs2 ps), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
	by(safe intro!: bisim1CallThrow elim!: bisim1_bsok bisims1_bsoks) simp
      moreover have "P \<turnstile>1 \<langle>null\<bullet>M'(map Val vs),(h, loc)\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer,(h, loc)\<rangle>"
	by(rule Red1CallNull)
      ultimately show ?thesis using exec pc \<tau> lenvs reds
	by(auto elim!: exec_meth.cases simp add: exec_move_def) fastsimp
    next
      assume ?rest
      then obtain a Ta where [simp]: "v = Addr a"
	and Ta: "typeof\<^bsub>h\<^esub> (Addr a) = \<lfloor>Ta\<rfloor>"
	and iec: "is_external_call P Ta M' (length vs)" by auto
      with exec pc wt lenvs
      obtain ta' va h'' U Ts where redex: "(ta', va, h'') \<in> set (red_external_list (compP2 P) a M' vs h)"
	and ret: "(xcp', h', [(stk', loc', arbitrary, arbitrary, pc')]) = extRet2JVM (length vs) h'' (rev vs @ [Addr a]) loc arbitrary arbitrary (length (compE2 obj) + length (compEs2 ps)) [] va"
	and wtext: "P \<turnstile> Ta\<bullet>M'(Ts) :: U"
	and Ts: "map typeof\<^bsub>h\<^esub> vs = map Some Ts"
	and ta': "ta = extTA2JVM (compP2 P) ta'"
	by(fastsimp elim!: exec_meth.cases is_ArrE simp add: is_Ref_def exec_move_def compP2_def has_method_def dest: sees_method_compPD external_call_not_sees_method[OF wf] split: heapobj.split_asm)
      from ret have [simp]: "h'' = h'" by simp
      from redex have redex': "P \<turnstile> \<langle>a\<bullet>M'(vs), h\<rangle> -ta'\<rightarrow>ext \<langle>va, h'\<rangle>"
	unfolding red_external_list_conv[symmetric] by(simp add: compP2_def)
      with Ta iec have "P \<turnstile>1 \<langle>addr a\<bullet>M'(map Val vs), (h, loc)\<rangle> -extTA2J1 P ta'\<rightarrow> \<langle>extRet2J va, (h', loc)\<rangle>"
	by -(rule Red1CallExternal, auto)
      moreover have "P,obj\<bullet>M'(ps),n,h' \<turnstile> (extRet2J va, loc) \<leftrightarrow> (stk', loc', pc', xcp')"
      proof(cases va)
	case (Inl v)
	have "P,obj\<bullet>M'(ps),n,h' \<turnstile> (Val v, loc) \<leftrightarrow> ([v], loc, length (compE2 (obj\<bullet>M'(ps))), None)"
	  by(rule bisim1Val2)(simp add: `bsok obj n` `bsoks ps n`)
	with ret Inl show ?thesis by simp
      next
	case (Inr ad)
	from lenvs have "length ps = length (rev vs)" by simp
	hence "P,obj\<bullet>M'(ps),n,h' \<turnstile> (Throw ad, loc) \<leftrightarrow> (rev vs @ [v], loc, length (compE2 (obj)) + length (compEs2 ps), \<lfloor>ad\<rfloor>)"
	  by(rule bisim1CallThrow)(simp_all add: `bsok obj n` `bsoks ps n`)
	with ret Inr show ?thesis by simp
      qed
      moreover from Ta have "h a \<noteq> None" by auto
      with ta' redex' external_call_hconf[OF redex' Ta Ts wtext hconf]
      have "ta_bisim (wbisim1 P) (extTA2J1 P ta') ta" by(auto intro: red_external_ta_bisim21[OF wf])
      ultimately show ?thesis using reds \<tau> pc by(fastsimp simp del: split_paired_Ex)
    qed
  qed
next
  case (bisim1CallThrowObj obj n a xs stk loc pc ps M')
  note exec = `?exec (obj\<bullet>M'(ps)) stk loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  note bisim1 = `P,obj,n,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)`
  from bisim1 have pc: "pc < length (compE2 obj)" by(auto dest: bisim1_ThrowD)
  from bisim1 have "match_ex_table (compP2 P) (cname_of h a) (0 + pc) (compxE2 obj 0 0) = None"
    unfolding compP2_def by(rule  bisim1_xcp_Some_not_caught)
  with exec pc have False
    by(auto elim!: exec_meth.cases simp add: exec_move_def match_ex_table_not_pcs_None)
  thus ?case ..
next
  case (bisim1CallThrowParams ps n vs a ps' xs stk loc pc obj M' v)
  note exec = `?exec (obj\<bullet>M'(ps)) (stk @ [v]) loc (length (compE2 obj) + pc) \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  note bisim2 = `P,ps,n,h \<turnstile> (map Val vs @ Throw a # ps', xs) [\<leftrightarrow>] (stk, loc, pc, \<lfloor>a\<rfloor>)`
  from bisim2 have pc: "pc < length (compEs2 ps)" by(auto dest: bisims1_ThrowD)
  from bisim2 have "match_ex_table (compP2 P) (cname_of h a) (0 + pc) (compxEs2 ps 0 0) = None"
    unfolding compP2_def by(rule bisims1_xcp_Some_not_caught)
  with exec pc have False
    apply(auto elim!: exec_meth.cases simp add: compxEs2_size_convs compxEs2_stack_xlift_convs exec_move_def)
    apply(auto simp add: match_ex_table_append dest!: match_ex_table_shift_pcD match_ex_table_stack_xliftD match_ex_table_pc_length_compE2)
    done
  thus ?case ..
next
  case (bisim1CallThrow ps vs obj n M' a xs v)
  note lenvs = `length ps = length vs`
  note exec = `?exec (obj\<bullet>M'(ps)) (vs @ [v]) xs (length (compE2 obj) + length (compEs2 ps)) \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  with lenvs have False
    by(auto elim!: exec_meth.cases simp add: match_ex_table_append_not_pcs exec_move_def dest!: match_ex_table_pc_length_compEs2)
  thus ?case ..
next
  case (bisim1BlockSome1 e V Ty v xs)
  have "\<tau>move2 {V:Ty=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub> 0 None" by(rule \<tau>move2BlockSome1)
  with `?exec {V:Ty=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub> [] xs 0 None stk' loc' pc' xcp'` `P,e,Suc V,h \<turnstile> (e, xs) \<leftrightarrow> ([], xs, 0, None)`
  show ?case by(fastsimp elim!: exec_meth.cases intro: \<tau>Red_refl bisim1BlockSome2 dest: bisim1_bsok simp add: exec_move_def)
next
  case (bisim1BlockSome2 e V Ty v xs)
  have "\<tau>move2 {V:Ty=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub> (Suc 0) None" by(rule \<tau>move2BlockSome2)
  with `?exec {V:Ty=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub> [v] xs (Suc 0) None stk' loc' pc' xcp'` `P,e,Suc V,h \<turnstile> (e, xs) \<leftrightarrow> ([], xs, 0, None)`
  show ?case by(fastsimp intro: \<tau>Red_refl bisim1BlockSome3[OF bisim1_refl] simp add: exec_move_def
                         elim!: exec_meth.cases dest: bisim1_bsok)
next
  case (bisim1BlockSome4 e V e' xs stk loc pc xcp Ty v)
  note IH = `\<And>stk' loc' pc' xcp' Env T. 
            \<lbrakk> ?exec e stk loc pc xcp stk' loc' pc' xcp'; Suc V + max_vars e' \<le> length xs; P,Env,h \<turnstile>1 e' : T \<rbrakk>
             \<Longrightarrow> \<exists>e'' xs''. P, e, Suc V, h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp') \<and> ?red e' xs e'' xs'' e pc xcp`
  note exec = `?exec {V:Ty=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub> stk loc (Suc (Suc pc)) xcp stk' loc' pc' xcp'`
  note bisim = `P,e,Suc V,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  from `V + max_vars {V:Ty=None; e'}\<^bsub>False\<^esub> \<le> length xs`
  have V: "V < length xs" and len: "Suc V + max_vars e' \<le> length xs" by simp_all
  from `P,Env,h \<turnstile>1 {V:Ty=None; e'}\<^bsub>False\<^esub> : T` have wt: "P,Env@[Ty],h \<turnstile>1 e' : T" by auto
  let ?pre = "[Push v, Store V]"
  from exec have exec': "exec_meth (compP2 P) (?pre @ compE2 e) (shift (length ?pre) (compxE2 e 0 0)) h (stk, loc, length ?pre + pc, xcp) ta h' (stk', loc', pc', xcp')"
    by(simp add: compxE2_size_convs exec_move_def)
  hence pc': "pc' \<ge> length ?pre"
    by(rule exec_meth_drop_pc) auto
  hence pc'': "Suc (Suc (pc' - Suc (Suc 0))) = pc'" by simp
  moreover from exec' have "exec_move P e h (stk, loc, pc, xcp) ta h' (stk', loc', pc' - length ?pre, xcp')"
    unfolding exec_move_def by(rule exec_meth_drop) auto
  from IH[OF this len wt] obtain e'' xs''
    where bisim': "P,e,Suc V,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc' - length ?pre, xcp')"
    and red': "?red e' xs e'' xs'' e pc xcp" by auto
  from bisim' have "P,{V:Ty=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub>,V,h' \<turnstile> ({V:Ty=None; e''}\<^bsub>False\<^esub>, xs'') \<leftrightarrow> (stk', loc', Suc (Suc (pc' - length ?pre)), xcp')"
    by(rule bisim1_bisims1.bisim1BlockSome4)
  moreover from pc' pc'' have "\<tau>move2 {V:Ty=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub> (Suc (Suc pc)) xcp = \<tau>move2 e pc xcp"
    by(auto intro: \<tau>move2BlockSome)
  moreover from red' have "length xs'' = length xs"
    by(auto split: split_if_asm dest!: \<tau>Red_preserves_len red1_preserves_len)
  ultimately show ?case using red' pc'' V
    by(fastsimp intro!: Block_None_\<tau>Red_xt Block1RedNone dest: \<tau>Red_preserves_len)
next
  case (bisim1BlockThrowSome e V a xs stk loc pc Ty v)
  note exec = `?exec {V:Ty=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub> stk loc (Suc (Suc pc)) \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  note bisim = `P,e,Suc V,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)`
  from bisim have pc: "pc < length (compE2 e)" by(auto dest: bisim1_ThrowD)
  from bisim have "match_ex_table (compP2 P) (cname_of h a) (0 + pc) (compxE2 e 0 0) = None"
    unfolding compP2_def by(rule  bisim1_xcp_Some_not_caught)
  with exec pc have False 
    apply(auto elim!: exec_meth.cases simp add: match_ex_table_not_pcs_None exec_move_def)
    apply(auto simp only: compxE2_size_convs dest!: match_ex_table_shift_pcD)
    apply simp
    done
  thus ?case ..
next
  case (bisim1BlockNone e V e' xs stk loc pc xcp Ty)
  note IH = `\<And>stk' loc' pc' xcp' Env T. 
            \<lbrakk> ?exec e stk loc pc xcp stk' loc' pc' xcp'; Suc V + max_vars e' \<le> length xs; P,Env,h \<turnstile>1 e' : T \<rbrakk>
             \<Longrightarrow> \<exists>e'' xs''. P, e, Suc V, h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp') \<and> ?red e' xs e'' xs'' e pc xcp`
  note exec = `?exec {V:Ty=None; e}\<^bsub>False\<^esub> stk loc pc xcp stk' loc' pc' xcp'`
  note bisim = `P,e,Suc V,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  from `V + max_vars {V:Ty=None; e'}\<^bsub>False\<^esub> \<le> length xs`
  have V: "V < length xs" and len: "Suc V + max_vars e' \<le> length xs" by simp_all
  from `P,Env,h \<turnstile>1 {V:Ty=None; e'}\<^bsub>False\<^esub> : T` have wt: "P,Env@[Ty],h \<turnstile>1 e' : T" by auto
  have "\<tau>move2 {V:Ty=None; e}\<^bsub>False\<^esub> pc xcp = \<tau>move2 e pc xcp"
    by(auto intro: \<tau>move2BlockNone)
  moreover
  from exec have "?exec e stk loc pc xcp stk' loc' pc' xcp'" by(simp add: exec_move_BlockNone)
  from IH[OF this len wt] obtain e'' xs''
    where bisim': "P,e,Suc V,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp')"
    and red': "?red e' xs e'' xs'' e pc xcp" by auto
  from red' have "length xs'' = length xs"
    by(auto split: split_if_asm dest!: \<tau>Red_preserves_len red1_preserves_len)
  moreover from bisim' have "P,{V:Ty=None; e}\<^bsub>False\<^esub>,V,h' \<turnstile> ({V:Ty=None; e''}\<^bsub>False\<^esub>, xs'') \<leftrightarrow> (stk', loc', pc', xcp')"
    by(rule bisim1_bisims1.bisim1BlockNone)
  ultimately show ?case using V red' apply auto
     apply(fastsimp)
    apply(frule \<tau>Red_preserves_len)
    apply(fastsimp elim!: Block1RedNone)
    done
next
  case (bisim1BlockThrowNone e V a xs stk loc pc Ty)
  note exec = `?exec {V:Ty=None; e}\<^bsub>False\<^esub> stk loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  note bisim = `P,e,Suc V,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)`
  from bisim have pc: "pc < length (compE2 e)" by(auto dest: bisim1_ThrowD)
  from bisim have "match_ex_table (compP2 P) (cname_of h a) (0 + pc) (compxE2 e 0 0) = None"
    unfolding compP2_def by(rule  bisim1_xcp_Some_not_caught)
  with exec pc have False by(auto elim!: exec_meth.cases simp add: exec_move_def)
  thus ?case ..
next
  case (bisim1Sync1 e1 V e' xs stk loc pc xcp e2)
  note IH = `\<And>stk' loc' pc' xcp' Env T. 
            \<lbrakk> ?exec e1 stk loc pc xcp stk' loc' pc' xcp'; V + max_vars e' \<le> length xs; P,Env,h \<turnstile>1 e' : T \<rbrakk>
             \<Longrightarrow> \<exists>e'' xs''. P, e1, V, h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp') \<and> ?red e' xs e'' xs'' e1 pc xcp`
  note exec = `?exec (sync\<^bsub>V\<^esub> (e1) e2) stk loc pc xcp stk' loc' pc' xcp'`
  note bisim = `P,e1,V,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim2 = `P,e2,Suc V,h \<turnstile> (e2, xs) \<leftrightarrow> ([], xs, 0, None)`
  note len = `V + max_vars (sync\<^bsub>V\<^esub> (e') e2) \<le> length xs`
  from `P,Env,h \<turnstile>1 (sync\<^bsub>V\<^esub> (e') e2) : T` obtain T' where wt: "P,Env,h \<turnstile>1 e' : T'" by auto
  from bisim have pc: "pc \<le> length (compE2 e1)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e1)")
    case True
    with exec have exec': "?exec e1 stk loc pc xcp stk' loc' pc' xcp'" by(simp add: exec_move_Sync1)
    from True have "\<tau>move2 (sync\<^bsub>V\<^esub> (e1) e2) pc xcp = \<tau>move2 e1 pc xcp" by(auto intro: \<tau>move2Sync1)
    with IH[OF exec' _ wt] len bisim2 show ?thesis
      by(fastsimp intro: bisim1_bisims1.bisim1Sync1 bisim1_bsok Synchronized1Red1)
  next
    case False
    with pc have [simp]: "pc = length (compE2 e1)" by simp
    with bisim obtain v where stk: "stk = [v]" and xcp: "xcp = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with bisim pc len have red: "\<tau>Red P h e' xs (Val v) loc" by(auto intro: bisim1_Val_\<tau>Red)
    hence "\<tau>Red P h (sync\<^bsub>V\<^esub> (e') e2) xs (sync\<^bsub>V\<^esub> (Val v) e2) loc" by auto
    moreover have \<tau>: "\<tau>move2 (sync\<^bsub>V\<^esub> (e1) e2) pc None"
      by(auto intro: \<tau>move2Sync2)
    moreover from bisim bisim2
    have "P,(sync\<^bsub>V\<^esub> (e1) e2),V,h \<turnstile> ((sync\<^bsub>V\<^esub> (Val v) e2), loc) \<leftrightarrow> ([], loc[V := v], Suc (length (compE2 e1)), None)"
      by(rule bisim1Sync2[OF bisim1_bsok bisim1_bsok])
    ultimately show ?thesis using exec stk xcp
      by(fastsimp elim!: exec_meth.cases simp add: exec_move_def)
  qed
next
  case (bisim1Sync2 e1 V e2 v xs)
  note exec = `?exec (sync\<^bsub>V\<^esub> (e1) e2) [] (xs[V := v]) (Suc (length (compE2 e1))) None stk' loc' pc' xcp'`
  note bisim = `P,e1,V,h \<turnstile> (e1, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim2 = `P,e2,Suc V,h \<turnstile> (e2, xs) \<leftrightarrow> ([], xs, 0, None)`
  have "\<tau>move2 (sync\<^bsub>V\<^esub> (e1) e2) (Suc (length (compE2 e1))) None" by(rule \<tau>move2Sync3)
  thus ?case using exec bisim bisim2
    by(fastsimp elim!: exec_meth.cases intro: bisim1Sync3 bisim1_bsok \<tau>Red_refl simp add: exec_move_def)
next
  case (bisim1Sync3 e1 V e2 v xs)
  note exec = `?exec (sync\<^bsub>V\<^esub> (e1) e2) [v] (xs[V := v]) (Suc (Suc (length (compE2 e1)))) None stk' loc' pc' xcp'`
  note bisim = `P,e1,V,h \<turnstile> (e1, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim2 = `\<And>xs. P,e2,Suc V,h \<turnstile> (e2, xs) \<leftrightarrow> ([], xs, 0, None)`
  note wt = `P,Env,h \<turnstile>1 sync\<^bsub>V\<^esub> (Val v) e2 : T`
  note len = `V + max_vars (sync\<^bsub>V\<^esub> (Val v) e2) \<le> length xs`
  hence V: "V < length xs" by simp
  have \<tau>: "\<not> \<tau>move2 (sync\<^bsub>V\<^esub> (e1) e2) (Suc (Suc (length (compE2 e1)))) None"
    by(fastsimp elim: \<tau>move2.cases dest: \<tau>move2_pc_length_compE2)
  from exec have "(\<exists>a. v = Addr a \<and> stk' = [] \<and> loc' = xs[V := v] \<and> ta = \<epsilon>\<lbrace>\<^bsub>l\<^esub> Lock\<rightarrow>a \<rbrace> \<and> xcp' = None \<and> pc' = Suc (Suc (Suc (length (compE2 e1))))) \<or> (v = Null \<and> stk' = [v] \<and> loc' = xs[V := v] \<and> ta = \<epsilon> \<and> xcp' = \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor> \<and> pc' = Suc (Suc (length (compE2 e1))))" (is "?c1 \<or> ?c2")
    by(fastsimp elim!: exec_meth.cases simp add: is_Ref_def expand_finfun_eq expand_fun_eq finfun_upd_apply exec_move_def)
  thus ?case
  proof
    assume ?c1
    then obtain a where [simp]: "v = Addr a" "stk' = []" "loc' = xs[V := v]" "ta = \<epsilon>\<lbrace>\<^bsub>l\<^esub>Lock\<rightarrow>a\<rbrace>"
      "xcp' = None" "pc' = Suc (Suc (Suc (length (compE2 e1))))" by blast    
    from wt obtain arrobj where "h a = \<lfloor>arrobj\<rfloor>" by auto
    hence "P \<turnstile>1 \<langle>sync\<^bsub>V\<^esub> (addr a) e2, (h, xs)\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub>Lock\<rightarrow>a\<rbrace>\<rightarrow> \<langle>insync\<^bsub>V\<^esub> (a) e2,(h, xs[V := Addr a])\<rangle>" using V
      by(rule Lock1Synchronized)
    moreover from bisim2 bisim1_bsok[OF bisim] have "P,sync\<^bsub>V\<^esub> (e1) e2,V,h \<turnstile> (insync\<^bsub>V\<^esub> (a) e2, xs[V := Addr a]) \<leftrightarrow> ([], xs[V := Addr a], Suc (Suc (Suc (length (compE2 e1)))), None)"
      by(auto intro: bisim1Sync4[where pc = 0, simplified])
    ultimately show ?case using exec \<tau>
      by(fastsimp elim!: exec_meth.cases split: split_if_asm simp add: is_Ref_def exec_move_def ta_bisim_def intro: \<tau>Red_refl)
  next
    assume ?c2
    hence [simp]: "v = Null" "stk' = [v]" "loc' = xs[V := v]" "ta = \<epsilon>" "xcp' = \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>"
      "pc' = Suc (Suc (length (compE2 e1)))" by simp_all
    from V have "P \<turnstile>1 \<langle>sync\<^bsub>V\<^esub> (null) e2, (h, xs)\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer,(h, xs[V := Null])\<rangle>"
      by(rule Synchronized1Null)
    moreover from bisim1_bsok[OF bisim] bisim1_bsok[OF bisim2]
    have "P,sync\<^bsub>V\<^esub> (e1) e2,V,h \<turnstile> (THROW NullPointer, xs[V := Null]) \<leftrightarrow> ([Null], xs[V := Null], Suc (Suc (length (compE2 e1))), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      by(rule bisim1Sync11)
    ultimately show ?case using exec \<tau>
      by(fastsimp elim!: exec_meth.cases split: split_if_asm simp add: is_Ref_def ta_bisim_def exec_move_def intro: \<tau>Red_refl)
  qed
next
  case (bisim1Sync4 e2 V e' xs stk loc pc xcp e1 a)
  note IH = `\<And>stk' loc' pc' xcp' Env T. 
            \<lbrakk> ?exec e2 stk loc pc xcp stk' loc' pc' xcp'; Suc V + max_vars e' \<le> length xs; P,Env,h \<turnstile>1 e' : T \<rbrakk>
             \<Longrightarrow> \<exists>e'' xs''. P, e2, Suc V, h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp') \<and> ?red e' xs e'' xs'' e2 pc xcp`
  note exec = `?exec (sync\<^bsub>V\<^esub> (e1) e2) stk loc (Suc (Suc (Suc (length (compE2 e1) + pc)))) xcp stk' loc' pc' xcp'`
  note bisim1 = `P,e1,V,h \<turnstile> (e1, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim2 = `P,e2,Suc V,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note len = `V + max_vars (insync\<^bsub>V\<^esub> (a) e') \<le> length xs`
  hence V: "V < length xs" and len': "Suc V + max_vars e' \<le> length xs" by simp_all
  from `P,Env,h \<turnstile>1 insync\<^bsub>V\<^esub> (a) e' : T` have wt: "P,Env@[Class Object],h \<turnstile>1 e' : T" by auto
  from bisim2 have pc: "pc \<le> length (compE2 e2)" by(rule bisim1_pc_length_compE2)
  let ?pre = "compE2 e1 @ [Store V, Load V, MEnter]"
  let ?post = "[Load V, MExit, Goto 4, Load V, MExit, Throw]"
  from exec have exec': "exec_meth (compP2 P) (?pre @ compE2 e2 @ ?post)
    (compxE2 e1 0 0 @ shift (length ?pre) (compxE2 e2 0 0 @ [(0, length (compE2 e2), Throwable, 3 + length (compE2 e2), 0)]))
    h (stk, loc, length ?pre + pc, xcp) ta h' (stk', loc', pc', xcp')"
    by(simp add: add_ac nat_number shift_compxE2 exec_move_def)
  hence pc': "pc' \<ge> length ?pre"
    by(rule exec_meth_drop_xt_pc[where n'=1]) auto
  from exec' have exec'': "exec_meth (compP2 P) (compE2 e2 @ ?post)
    (compxE2 e2 0 0 @ [(0, length (compE2 e2), Throwable, 3 + length (compE2 e2), 0)])
    h (stk, loc, pc, xcp) ta h' (stk', loc', pc' - length ?pre, xcp')"
    by(rule exec_meth_drop_xt[where n=1]) auto
  show ?case
  proof(cases "pc < length (compE2 e2)")
    case True
    note pc = True
    hence \<tau>: "\<tau>move2 (sync\<^bsub>V\<^esub> (e1) e2) (Suc (Suc (Suc (length (compE2 e1) + pc)))) xcp = \<tau>move2 e2 pc xcp"
      by(auto intro: \<tau>move2Sync4)
    show ?thesis
    proof(cases "xcp = None \<or> (\<exists>a'. xcp = \<lfloor>a'\<rfloor> \<and> match_ex_table (compP2 P) (cname_of h a') pc (compxE2 e2 0 0) \<noteq> None)")
      case False
      then obtain a' where Some: "xcp = \<lfloor>a'\<rfloor>" 
	and True: "match_ex_table (compP2 P) (cname_of h a') pc (compxE2 e2 0 0) = None" by(auto simp del: not_None_eq)
      from Some bisim2 wt have "\<exists>C. typeof\<^bsub>h\<^esub> (Addr a') = \<lfloor>Class C\<rfloor> \<and> P \<turnstile> C \<preceq>\<^sup>* Throwable"
	by -(rule bisim1_WTrt1_Throw_ObjD, auto)
      then obtain C' fs where ha': "h a' = \<lfloor>Obj C' fs\<rfloor>" and subcls: "P \<turnstile> C' \<preceq>\<^sup>* Throwable" by(auto split: heapobj.split_asm)
      from ha' subcls bisim2 True have "\<tau>Red P h e' xs (Throw a') loc"
	using len' unfolding Some compP2_def by(blast dest: bisim1_xcp_\<tau>Red)
      moreover from pc have "\<tau>move2 (sync\<^bsub>V\<^esub> (e1) e2) (Suc (Suc (Suc (pc + length (compE2 e1))))) \<lfloor>a'\<rfloor>"
	by(auto intro: \<tau>move2xcp)
      moreover from bisim1_bsok[OF bisim1] bisim1_bsok[OF bisim2]
      have "P, sync\<^bsub>V\<^esub> (e1) e2, V, h \<turnstile> (insync\<^bsub>V\<^esub> (a) Throw a', loc) \<leftrightarrow> ([Addr a'], loc, 6 + length (compE2 e1) + length (compE2 e2), None)"
	by(rule bisim1Sync7)
      ultimately show ?thesis using exec True pc Some ha' subcls
	apply(auto elim!: exec_meth.cases simp add: add_ac nat_number match_ex_table_append matches_ex_entry_def compP2_def exec_move_def)
	apply fastsimp
	apply(simp only: compxE2_size_convs, auto dest: match_ex_table_shift_pcD match_ex_table_pc_length_compE2)
	done
    next
      case True 
      with exec'' pc have "exec_meth (compP2 P) (compE2 e2 @ ?post) (compxE2 e2 0 0)
	h (stk, loc, pc, xcp) ta h' (stk', loc', pc' - length ?pre, xcp')"
	by(auto elim!: exec_meth.cases intro: exec_meth.intros simp add: match_ex_table_append exec_move_def)
      hence "exec_move P e2 h (stk, loc, pc, xcp) ta h' (stk', loc', pc' - length ?pre, xcp')"
	using pc unfolding exec_move_def by(rule exec_meth_take)
      from IH[OF this len' wt] obtain e'' xs''
	where bisim': "P,e2,Suc V,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc' - length ?pre, xcp')"
	and red': "?red e' xs e'' xs'' e2 pc xcp" by auto
      from bisim' bisim1_bsok[OF bisim1]
      have "P,sync\<^bsub>V\<^esub> (e1) e2, V,h' \<turnstile> (insync\<^bsub>V\<^esub> (a) e'', xs'') \<leftrightarrow> (stk', loc', Suc (Suc (Suc (length (compE2 e1) + (pc' - length ?pre)))), xcp')"
	by(rule bisim1_bisims1.bisim1Sync4)
      moreover from pc' have "Suc (Suc (Suc (length (compE2 e1) + (pc' - Suc (Suc (Suc (length (compE2 e1)))))))) = pc'"
	"Suc (Suc (Suc (pc' - Suc (Suc (Suc 0))))) = pc'"
	by simp_all
      ultimately show ?thesis using red' \<tau> by(fastsimp intro: Synchronized1Red2 simp add: nat_number)
    qed
  next
    case False
    with pc have [simp]: "pc = length (compE2 e2)" by simp
    with bisim2 obtain v where [simp]: "stk = [v]" "xcp = None" by(auto dest: bisim1_pc_length_compE2D)
    have "\<tau>move2 (sync\<^bsub>V\<^esub> (e1) e2) (Suc (Suc (Suc (length (compE2 e1) + length (compE2 e2))))) None"
      by(rule \<tau>move2Sync5)
    moreover from bisim2 pc len have red: "\<tau>Red P h e' xs (Val v) loc" by(auto intro: bisim1_Val_\<tau>Red)
    hence "\<tau>Red P h (insync\<^bsub>V\<^esub> (a) e') xs (insync\<^bsub>V\<^esub> (a) (Val v)) loc" by auto
    moreover from bisim1_bsok[OF bisim1] bisim1_bsok[OF bisim2]
    have "P,sync\<^bsub>V\<^esub> (e1) e2,V,h \<turnstile> (insync\<^bsub>V\<^esub> (a) (Val v), loc) \<leftrightarrow> ([loc ! V, v], loc, 4 + length (compE2 e1) + length (compE2 e2), None)"
      by(rule bisim1Sync5)
    ultimately show ?thesis using exec
      by(auto elim!: exec_meth.cases simp add: nat_number exec_move_def) blast
  qed
next
  case (bisim1Sync5 e1 V e2 a v xs)
  note bisim1 = `P,e1,V,h \<turnstile> (e1, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim2 = `P,e2,Suc V,h \<turnstile> (e2, xs) \<leftrightarrow> ([], xs, 0, None)`
  note exec = `?exec (sync\<^bsub>V\<^esub> (e1) e2) [xs ! V, v] xs (4 + length (compE2 e1) + length (compE2 e2)) None stk' loc' pc' xcp'`
  from `V + max_vars (insync\<^bsub>V\<^esub> (a) Val v) \<le> length xs` have V: "V < length xs" by simp
  have \<tau>: "\<not> \<tau>move2 (sync\<^bsub>V\<^esub> (e1) e2) (4 + length (compE2 e1) + length (compE2 e2)) None"
    by(fastsimp elim: \<tau>move2.cases dest: \<tau>move2_pc_length_compE2)
  have \<tau>': "\<not> \<tau>move1 (insync\<^bsub>V\<^esub> (a) Val v)" by auto
  from exec have "(\<exists>a'. xs ! V = Addr a') \<or> xs ! V = Null" (is "?c1 \<or> ?c2")
    by(auto elim!: exec_meth.cases simp add: split_beta is_Ref_def exec_move_def split: split_if_asm)
  thus ?case
  proof
    assume ?c1
    then obtain a' where xsV [simp]: "xs ! V = Addr a'" ..
    from bisim1_bsok[OF bisim1] bisim1_bsok[OF bisim2]
    have "P,sync\<^bsub>V\<^esub> (e1) e2,V,h \<turnstile> (Val v, xs) \<leftrightarrow> ([v], xs, 5 + length (compE2 e1) + length (compE2 e2), None)"
      "P,sync\<^bsub>V\<^esub> (e1) e2,V,h \<turnstile> (THROW IllegalMonitorState,xs) \<leftrightarrow> ([Addr a', v],xs,4 + length (compE2 e1) + length (compE2 e2),\<lfloor>addr_of_sys_xcpt IllegalMonitorState\<rfloor>)"
      by(rule bisim1Sync6, rule bisim1Sync13)
    moreover from xsV V have "P \<turnstile>1 \<langle>insync\<^bsub>V\<^esub> (a) Val v, (h, xs)\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a' \<rbrace>\<rightarrow> \<langle>Val v,(h, xs)\<rangle>"
      by(rule Unlock1Synchronized)
    moreover from xsV V have "P \<turnstile>1 \<langle>insync\<^bsub>V\<^esub> (a) Val v, (h, xs)\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub> UnlockFail\<rightarrow>a' \<rbrace>\<rightarrow> \<langle>THROW IllegalMonitorState,(h, xs)\<rangle>"
      by(rule Unlock1SynchronizedFail)
    ultimately show ?case using \<tau> \<tau>' exec
      by(fastsimp elim!: exec_meth.cases intro: \<tau>Red_refl simp add: is_Ref_def ta_bisim_def add_ac exec_move_def)
  next
    assume xsV: "xs ! V = Null"
    from bisim1_bsok[OF bisim1] bisim1_bsok[OF bisim2]
    have "P,sync\<^bsub>V\<^esub> (e1) e2,V,h \<turnstile> (THROW NullPointer,xs) \<leftrightarrow> ([Null, v],xs,4 + length (compE2 e1) + length (compE2 e2),\<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      by(rule bisim1Sync12)
    thus ?case using \<tau> \<tau>' exec xsV V
      by(fastsimp elim!: exec_meth.cases intro: \<tau>Red_refl Unlock1SynchronizedNull simp add: is_Ref_def ta_bisim_def add_ac exec_move_def)
  qed
next
  case (bisim1Sync6 e1 V e2 v x)
  note bisim1 = `P,e1,V,h \<turnstile> (e1, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim2 = `P,e2,Suc V,h \<turnstile> (e2, xs) \<leftrightarrow> ([], xs, 0, None)`
  note exec = `?exec (sync\<^bsub>V\<^esub> (e1) e2) [v] x (5 + length (compE2 e1) + length (compE2 e2)) None stk' loc' pc' xcp'`
  have "\<tau>move2 (sync\<^bsub>V\<^esub> (e1) e2) (5 + length (compE2 e1) + length (compE2 e2)) None"
    by(rule \<tau>move2Sync6)
  moreover from bisim1_bsok[OF bisim1] bisim1_bsok[OF bisim2]
  have "P,sync\<^bsub>V\<^esub> (e1) e2,V,h \<turnstile> (Val v, x) \<leftrightarrow> ([v], x, length (compE2 (sync\<^bsub>V\<^esub> (e1) e2)), None)"
    by-(rule bisim1Val2, auto)
  moreover have "nat (9 + (int (length (compE2 e1)) + int (length (compE2 e2)))) = 9 + length (compE2 e1) + length (compE2 e2)" by arith
  ultimately show ?case using exec
    by(fastsimp elim!: exec_meth.cases intro: \<tau>Red_refl simp add: nat_number exec_move_def)
next
  case (bisim1Sync7 e1 V e2 a a' xs)
  note bisim1 = `P,e1,V,h \<turnstile> (e1, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim2 = `P,e2,Suc V,h \<turnstile> (e2, xs) \<leftrightarrow> ([], xs, 0, None)`
  note exec = `?exec (sync\<^bsub>V\<^esub> (e1) e2) [Addr a'] xs (6 + length (compE2 e1) + length (compE2 e2)) None stk' loc' pc' xcp'`

  moreover from bisim1_bsok[OF bisim1] bisim1_bsok[OF bisim2]
  have "P,sync\<^bsub>V\<^esub> (e1) e2,V,h' \<turnstile> (insync\<^bsub>V\<^esub> (a) Throw a', xs) \<leftrightarrow>
        ([xs ! V, Addr a'], xs, 7 + length (compE2 e1) + length (compE2 e2), None)"
    by(rule bisim1Sync8)
  moreover have "\<tau>move2 (sync\<^bsub>V\<^esub> (e1) e2) (6 + length (compE2 e1) + length (compE2 e2)) None"
    by(rule \<tau>move2Sync7)
  ultimately show ?case by(fastsimp elim!: exec_meth.cases intro: \<tau>Red_refl simp add: nat_number exec_move_def)
next
  case (bisim1Sync8 e1 V e2 a a' xs)
  note bisim1 = `P,e1,V,h \<turnstile> (e1, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim2 = `P,e2,Suc V,h \<turnstile> (e2, xs) \<leftrightarrow> ([], xs, 0, None)`
  note len = `V + max_vars (insync\<^bsub>V\<^esub> (a) Throw a') \<le> length xs`
  hence V: "V < length xs" by simp
  note exec = `?exec (sync\<^bsub>V\<^esub> (e1) e2) [xs ! V, Addr a'] xs (7 + length (compE2 e1) + length (compE2 e2)) None stk' loc' pc' xcp'`
  moreover have "\<not> \<tau>move2 (sync\<^bsub>V\<^esub> (e1) e2) (7 + length (compE2 e1) + length (compE2 e2)) None"
    by(fastsimp elim: \<tau>move2.cases dest: \<tau>move2_pc_length_compE2)
  moreover from bisim1_bsok[OF bisim1] bisim1_bsok[OF bisim2]
  have "P,sync\<^bsub>V\<^esub> (e1) e2,V,h \<turnstile> (Throw a', xs) \<leftrightarrow> ([Addr a'], xs, 8 + length (compE2 e1) + length (compE2 e2), None)"
    "P,sync\<^bsub>V\<^esub> (e1) e2,V,h \<turnstile> (THROW IllegalMonitorState,xs) \<leftrightarrow> ([xs ! V, Addr a'],xs,7 + length (compE2 e1) + length (compE2 e2),\<lfloor>addr_of_sys_xcpt IllegalMonitorState\<rfloor>)"
    "P,sync\<^bsub>V\<^esub> (e1) e2,V,h \<turnstile> (THROW NullPointer,xs) \<leftrightarrow> ([Null, Addr a'],xs,7 + length (compE2 e1) + length (compE2 e2),\<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
    by(rule bisim1Sync9 bisim1Sync14 bisim1Sync15)+
  moreover {
    fix A
    assume "xs ! V = Addr A"
    hence "P \<turnstile>1 \<langle>insync\<^bsub>V\<^esub> (a) Throw a',(h, xs)\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>A\<rbrace>\<rightarrow> \<langle>Throw a', (h, xs)\<rangle>"
      "P \<turnstile>1 \<langle>insync\<^bsub>V\<^esub> (a) Throw a',(h, xs)\<rangle> -\<epsilon>\<lbrace>\<^bsub>l\<^esub> UnlockFail\<rightarrow>A\<rbrace>\<rightarrow> \<langle>THROW IllegalMonitorState, (h, xs)\<rangle>"
      using V by(rule Synchronized1Throw2 Synchronized1Throw2Fail)+ }
  moreover {
    assume "xs ! V = Null"
    hence "P \<turnstile>1 \<langle>insync\<^bsub>V\<^esub> (a) Throw a',(h, xs)\<rangle> -\<epsilon>\<rightarrow> \<langle>THROW NullPointer, (h, xs)\<rangle>"
      using V by(rule Synchronized1Throw2Null) }
  moreover have "\<not> \<tau>move1 (insync\<^bsub>V\<^esub> (a) Throw a')" by fastsimp
  ultimately show ?case
    by(fastsimp elim!: exec_meth.cases intro: \<tau>Red_refl simp add: nat_number is_Ref_def ta_bisim_def exec_move_def split: split_if_asm)
next
  case (bisim1Sync9 e1 V e2 a xs)
  note bisim1 = `P,e1,V,h \<turnstile> (e1, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim2 = `P,e2,Suc V,h \<turnstile> (e2, xs) \<leftrightarrow> ([], xs, 0, None)`
  note exec = `?exec (sync\<^bsub>V\<^esub> (e1) e2) [Addr a] xs (8 + length (compE2 e1) + length (compE2 e2)) None stk' loc' pc' xcp'`
  moreover from bisim1_bsok[OF bisim1] bisim1_bsok[OF bisim2]
  have "P,sync\<^bsub>V\<^esub> (e1) e2,V,h \<turnstile> (Throw a, xs) \<leftrightarrow> ([Addr a], xs, 8 + length (compE2 e1) + length (compE2 e2), \<lfloor>a\<rfloor>)"
    by(rule bisim1Sync10)
  moreover have "\<tau>move2 (sync\<^bsub>V\<^esub> (e1) e2) (8 + length (compE2 e1) + length (compE2 e2)) None"
    by(rule \<tau>move2Sync8)
  ultimately show ?case 
    by(fastsimp elim!: exec_meth.cases intro: \<tau>Red_refl simp add: nat_number exec_move_def split: split_if_asm)
next
  case (bisim1Sync10 e1 V e2 a xs)
  from `?exec (sync\<^bsub>V\<^esub> (e1) e2) [Addr a] xs (8 + length (compE2 e1) + length (compE2 e2)) \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  have False by(auto elim!: exec_meth.cases simp add: matches_ex_entry_def match_ex_table_append_not_pcs exec_move_def)
  thus ?case ..
next
  case (bisim1Sync11 e1 V e2 xs)
  from `?exec (sync\<^bsub>V\<^esub> (e1) e2) [Null] xs (Suc (Suc (length (compE2 e1)))) \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor> stk' loc' pc' xcp'`
  have False by(auto elim!: exec_meth.cases simp add: matches_ex_entry_def match_ex_table_append_not_pcs exec_move_def)
  thus ?case ..
next
  case (bisim1Sync12 e1 V e2 xs v)
  from `?exec (sync\<^bsub>V\<^esub> (e1) e2) [Null, v] xs (4 + length (compE2 e1) + length (compE2 e2)) \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor> stk' loc' pc' xcp'`
  have False by(auto elim!: exec_meth.cases simp add: matches_ex_entry_def match_ex_table_append_not_pcs exec_move_def)
  thus ?case ..
next
  case (bisim1Sync13 e1 V e2 xs v' v)
  from `?exec (sync\<^bsub>V\<^esub> (e1) e2) [v', v] xs (4 + length (compE2 e1) + length (compE2 e2)) \<lfloor>addr_of_sys_xcpt IllegalMonitorState\<rfloor> stk' loc' pc' xcp'`
  have False by(auto elim!: exec_meth.cases simp add: matches_ex_entry_def match_ex_table_append_not_pcs exec_move_def)
  thus ?case ..
next
  case (bisim1Sync14 e1 V e2 xs v a')
  from `?exec (sync\<^bsub>V\<^esub> (e1) e2) [v, Addr a'] xs (7 + length (compE2 e1) + length (compE2 e2)) \<lfloor>addr_of_sys_xcpt IllegalMonitorState\<rfloor> stk' loc' pc' xcp'`
  have False by(auto elim!: exec_meth.cases simp add: matches_ex_entry_def match_ex_table_append_not_pcs exec_move_def)
  thus ?case ..
next
  case (bisim1Sync15 e1 V e2 xs a')
  from `?exec (sync\<^bsub>V\<^esub> (e1) e2) [Null, Addr a'] xs (7 + length (compE2 e1) + length (compE2 e2)) \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor> stk' loc' pc' xcp'`
  have False by(auto elim!: exec_meth.cases simp add: matches_ex_entry_def match_ex_table_append_not_pcs exec_move_def)
  thus ?case ..
next
  case (bisim1SyncThrow e1 V a xs stk loc pc e2)
  note exec = `?exec (sync\<^bsub>V\<^esub> (e1) e2) stk loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  note bisim1 = `P,e1,V,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)`
  from bisim1 have pc: "pc < length (compE2 e1)" by(auto dest: bisim1_ThrowD)
  from bisim1 have "match_ex_table (compP2 P) (cname_of h a) (0 + pc) (compxE2 e1 0 0) = None"
    unfolding compP2_def by(rule  bisim1_xcp_Some_not_caught)
  with exec pc have False
    apply(auto elim!: exec_meth.cases simp add: match_ex_table_append_not_pcs exec_move_def)
    apply(auto dest!: match_ex_table_shift_pcD simp add: matches_ex_entry_def)
    done
  thus ?case ..
next
  case (bisim1Seq1 e1 n e' xs stk loc pc xcp e2)
  note IH = `\<And>stk' loc' pc' xcp' Env' T. 
            \<lbrakk> ?exec e1 stk loc pc xcp stk' loc' pc' xcp'; n + max_vars e' \<le> length xs; P,Env,h \<turnstile>1 e' : T \<rbrakk>
             \<Longrightarrow> \<exists>e'' xs''. P, e1, n, h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp') \<and> ?red e' xs e'' xs'' e1 pc xcp`
  note exec = `?exec (e1;; e2) stk loc pc xcp stk' loc' pc' xcp'`
  note bisim = `P,e1,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note len = `n + max_vars (e';;e2) \<le> length xs`
  from `P,Env,h \<turnstile>1 e';;e2 : T` obtain T' where wt: "P,Env,h \<turnstile>1 e' : T'" by auto
  from bisim have pc: "pc \<le> length (compE2 e1)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e1)")
    case True
    let ?post = "Pop # compE2 e2"
    from exec have exec': "?exec e1 stk loc pc xcp stk' loc' pc' xcp'" using True by(simp add: exec_move_Seq1)
    from True have "\<tau>move2 (e1;;e2) pc xcp = \<tau>move2 e1 pc xcp" by(auto intro: \<tau>move2Seq1)
    with IH[OF exec' _ wt] len bisim1_bsok[OF `P,e2,n,h \<turnstile> (e2, xs) \<leftrightarrow> ([], xs, 0, None)`] show ?thesis
      by(fastsimp intro: bisim1_bisims1.bisim1Seq1 bisim1_bsok Seq1Red)
  next
    case False
    with pc have [simp]: "pc = length (compE2 e1)" by simp
    with bisim obtain v where stk: "stk = [v]" and xcp: "xcp = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with bisim pc len have red: "\<tau>Red P h e' xs (Val v) loc" by(auto intro: bisim1_Val_\<tau>Red)
    hence "\<tau>Red P h (e';; e2) xs (Val v;;e2) loc" by auto
    moreover have \<tau>: "\<not> \<tau>move2 (e1;;e2) pc None"
      by(auto elim: \<tau>move2.cases dest: \<tau>move2_pc_length_compE2)
    moreover have "\<not> \<tau>move1 (Val v;;e2)" by auto
    moreover from `P,e2,n,h \<turnstile> (e2, loc) \<leftrightarrow> ([], loc, 0, None)` bisim
    have "P,e1;;e2,n,h \<turnstile> (e2, loc) \<leftrightarrow> ([], loc, Suc (length (compE2 e1) + 0), None)"
      by(rule bisim1Seq2[OF _ bisim1_bsok])
    ultimately show ?thesis using exec stk xcp
      by(fastsimp elim!: exec_meth.cases intro: Red1Seq simp add: exec_move_def)
  qed
next
  case (bisim1SeqThrow1 e1 n a xs stk loc pc e2)
  note exec = `?exec (e1;;e2) stk loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  note bisim1 = `P,e1,n,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)`
  from bisim1 have pc: "pc < length (compE2 e1)" by(auto dest: bisim1_ThrowD)
  from bisim1 have "match_ex_table (compP2 P) (cname_of h a) (0 + pc) (compxE2 e1 0 0) = None"
    unfolding compP2_def by(rule  bisim1_xcp_Some_not_caught)
  with exec pc have False
    by(auto elim!: exec_meth.cases simp add: match_ex_table_not_pcs_None exec_move_def)
  thus ?case ..
next
  case (bisim1Seq2 e2 n e' xs stk loc pc xcp e1)
  note IH = `\<And>stk' loc' pc' xcp' Env' T. 
            \<lbrakk> ?exec e2 stk loc pc xcp stk' loc' pc' xcp'; n + max_vars e' \<le> length xs; P,Env,h \<turnstile>1 e' : T \<rbrakk>
             \<Longrightarrow> \<exists>e'' xs''. P, e2, n, h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp') \<and> ?red e' xs e'' xs'' e2 pc xcp`
  note bisim1 = `\<And>xs. P,e1,n,h \<turnstile> (e1, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim2 = `P,e2,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note len = `n + max_vars e' \<le> length xs`
  note wt = `P,Env,h \<turnstile>1 e' : T`
  note exec = `?exec (e1;; e2) stk loc (Suc (length (compE2 e1) + pc)) xcp stk' loc' pc' xcp'`
  let ?pre = "compE2 e1 @ [Pop]"
  from exec have exec': "exec_meth (compP2 P) (?pre @ compE2 e2) (compxE2 e1 0 0 @ shift (length ?pre) (compxE2 e2 0 0)) h (stk, loc, length ?pre + pc, xcp) ta h' (stk', loc', pc', xcp')"
    by(simp add: shift_compxE2 exec_move_def)
  hence "?exec e2 stk loc pc xcp stk' loc' (pc' - length ?pre) xcp'"
    unfolding exec_move_def by(rule exec_meth_drop_xt, auto)
  from IH[OF this len wt] obtain e'' xs''
    where bisim': "P,e2,n,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc' - length ?pre, xcp')"
    and red: "?red e' xs e'' xs'' e2 pc xcp" by auto
  from bisim' bisim1_bsok[OF bisim1]
  have "P,e1;;e2,n,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', Suc (length (compE2 e1) + (pc' - length ?pre)), xcp')"
    by(rule bisim1_bisims1.bisim1Seq2)
  moreover have \<tau>: "\<tau>move2 (e1;;e2) (Suc (length (compE2 e1) + pc)) xcp = \<tau>move2 e2 pc xcp"
    by(auto intro: \<tau>move2Seq2)
  moreover from exec' have "pc' \<ge> length ?pre"
    by(rule exec_meth_drop_xt_pc) auto
  ultimately show ?case using red by fastsimp
next
  case (bisim1Cond1 e n e' xs stk loc pc xcp e1 e2)
  note IH = `\<And>stk' loc' pc' xcp' Env' T. 
            \<lbrakk> ?exec e stk loc pc xcp stk' loc' pc' xcp'; n + max_vars e' \<le> length xs; P,Env,h \<turnstile>1 e' : T \<rbrakk>
             \<Longrightarrow> \<exists>e'' xs''. P, e, n, h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp') \<and> ?red e' xs e'' xs'' e pc xcp`
  note bisim = `P,e,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim1 = `\<And>xs. P,e1,n,h \<turnstile> (e1, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim2 = `\<And>xs. P,e2,n,h \<turnstile> (e2, xs) \<leftrightarrow> ([], xs, 0, None)`
  from `n + max_vars (if (e') e1 else e2) \<le> length xs`
  have len: "n + max_vars e' \<le> length xs" by simp
  from `P,Env,h \<turnstile>1 if (e') e1 else e2 : T` have wt: "P,Env,h \<turnstile>1 e' : Boolean" by auto
  note exec = `?exec (if (e) e1 else e2) stk loc pc xcp stk' loc' pc' xcp'`
  from bisim have pc: "pc \<le> length (compE2 e)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e)")
    case True
    let ?post = "IfFalse (2 + int (length (compE2 e1))) # compE2 e1 @ Goto (1 + int (length (compE2 e2))) # compE2 e2"
    from exec have exec': "?exec e stk loc pc xcp stk' loc' pc' xcp'" using True
      by(simp add: exec_move_Cond1)
    from True have "\<tau>move2 (if (e) e1 else e2) pc xcp = \<tau>move2 e pc xcp" by(auto intro: \<tau>move2Cond)
    with IH[OF exec' _ wt] len bisim1_bsok[OF bisim1] bisim1_bsok[OF bisim2] show ?thesis
      by(fastsimp intro: bisim1_bisims1.bisim1Cond1 Cond1Red)
  next
    case False
    with pc have [simp]: "pc = length (compE2 e)" by simp
    with bisim obtain v where stk: "stk = [v]" and xcp: "xcp = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with bisim pc len have red: "\<tau>Red P h e' xs (Val v) loc" by(auto intro: bisim1_Val_\<tau>Red)
    hence "\<tau>Red P h (if (e') e1 else e2) xs (if (Val v) e1 else e2) loc" by auto
    moreover have \<tau>: "\<not> \<tau>move2 (if (e) e1 else e2) pc None"
      by(auto elim: \<tau>move2.cases dest: \<tau>move2_pc_length_compE2)
    moreover have "\<not> \<tau>move1 (if (Val v) e1 else e2)" by auto
    moreover from bisim1[of loc] bisim1_bsok[OF bisim] bisim1_bsok[OF bisim2]
    have "P,if (e) e1 else e2,n,h \<turnstile> (e1, loc) \<leftrightarrow> ([], loc, Suc (length (compE2 e) + 0), None)"
      by(rule bisim1CondThen)
    moreover from bisim2[of loc] bisim1_bsok[OF bisim] bisim1_bsok[OF bisim1]
    have "P,if (e) e1 else e2,n,h \<turnstile> (e2, loc) \<leftrightarrow> ([], loc, Suc (Suc (length (compE2 e) + length (compE2 e1) + 0)), None)"
      by(rule bisim1CondElse)
    moreover have "nat (int (length (compE2 e)) + (2 + int (length (compE2 e1)))) = Suc (Suc (length (compE2 e) + length (compE2 e1) + 0))" by simp
    moreover from bisim stk xcp wt have "P,Env,h \<turnstile>1 Val v : Boolean"
      by(auto dest: bisim1_length_compE2_WTrt_eq)
    ultimately show ?thesis using exec stk xcp
      by(fastsimp elim!: exec_meth.cases intro: Red1CondT Red1CondF simp add: nat_number exec_move_def)
  qed
next
  case (bisim1CondThen e1 n e' xs stk loc pc xcp e e2)
  note IH = `\<And>stk' loc' pc' xcp' Env' T. 
            \<lbrakk> ?exec e1 stk loc pc xcp stk' loc' pc' xcp'; n + max_vars e' \<le> length xs; P,Env,h \<turnstile>1 e' : T \<rbrakk>
             \<Longrightarrow> \<exists>e'' xs''. P, e1, n, h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp') \<and> ?red e' xs e'' xs'' e1 pc xcp`
  note bisim1 = `P,e1,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim = `\<And>xs. P,e,n,h \<turnstile> (e, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim2 = `\<And>xs. P,e2,n,h \<turnstile> (e2, xs) \<leftrightarrow> ([], xs, 0, None)`
  note len = `n + max_vars e' \<le> length xs`
  note wt = `P,Env,h \<turnstile>1 e' : T`
  note exec = `?exec (if (e) e1 else e2) stk loc (Suc (length (compE2 e) + pc)) xcp stk' loc' pc' xcp'`
  from bisim1 have pc: "pc \<le> length (compE2 e1)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e1)")
    case True
    let ?pre = "compE2 e @ [IfFalse (2 + int (length (compE2 e1)))]"
    let ?post = "Goto (1 + int (length (compE2 e2))) # compE2 e2"
    from exec have exec': "exec_meth (compP2 P) (?pre @ compE2 e1 @ ?post)
      (compxE2 e 0 0 @ shift (length ?pre) (compxE2 e1 0 0 @ shift (length (compE2 e1)) (compxE2 e2 (Suc 0) 0)))
      h (stk, loc, length ?pre + pc, xcp) ta h' (stk', loc', pc', xcp')"
      by(simp add: shift_compxE2 add_ac exec_move_def)
    hence "exec_meth (compP2 P) (compE2 e1 @ ?post) (compxE2 e1 0 0 @ shift (length (compE2 e1)) (compxE2 e2 (Suc 0) 0))
      h (stk, loc, pc, xcp) ta h' (stk', loc', pc' - length ?pre, xcp')"
      by(rule exec_meth_drop_xt) auto
    hence "exec_move P e1 h (stk, loc, pc, xcp) ta h' (stk', loc', pc' - length ?pre, xcp')"
      using True unfolding exec_move_def by(rule exec_meth_take_xt)
    from IH[OF this len wt] obtain e'' xs''
      where bisim': "P,e1,n,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc' - length ?pre, xcp')"
      and red: "?red e' xs e'' xs'' e1 pc xcp" by auto
    from bisim' bisim1_bsok[OF bisim] bisim1_bsok[OF bisim2]
    have "P,if (e) e1 else e2,n,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', Suc (length (compE2 e) + (pc' - length ?pre)), xcp')"
      by(rule bisim1_bisims1.bisim1CondThen)
    moreover from True have \<tau>: "\<tau>move2 (if (e) e1 else e2) (Suc (length (compE2 e) + pc)) xcp = \<tau>move2 e1 pc xcp"
      by(auto intro: \<tau>move2CondThen)
    moreover from exec' have "pc' \<ge> length ?pre"
      by(rule exec_meth_drop_xt_pc) auto
    ultimately show ?thesis using red by fastsimp
  next
    case False
    with pc have [simp]: "pc = length (compE2 e1)" by simp
    with bisim1 obtain v where stk: "stk = [v]" and xcp: "xcp = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with bisim1 pc len have red: "\<tau>Red P h e' xs (Val v) loc" by(auto intro: bisim1_Val_\<tau>Red)
    moreover have \<tau>: "\<tau>move2 (if (e) e1 else e2) (Suc (length (compE2 e) + length (compE2 e1))) None"
      by(rule \<tau>move2CondThenExit)
    moreover from bisim1_bsok[OF bisim] bisim1_bsok[OF bisim1] bisim1_bsok[OF bisim2]
    have "bsok (if (e) e1 else e2) n" by simp
    hence "P,if (e) e1 else e2,n,h \<turnstile> (Val v, loc) \<leftrightarrow> ([v], loc, length (compE2 (if (e) e1 else e2)), None)"
      by(rule bisim1Val2)
    moreover have "nat (2 + (int (length (compE2 e)) + (int (length (compE2 e1)) + int (length (compE2 e2))))) = length (compE2 (if (e) e1 else e2))" by simp
    ultimately show ?thesis using exec xcp stk by(fastsimp elim!: exec_meth.cases simp add: exec_move_def)
  qed
next
  case (bisim1CondElse e2 n e' xs stk loc pc xcp e e1)
  note IH = `\<And>stk' loc' pc' xcp' Env' T. 
            \<lbrakk> ?exec e2 stk loc pc xcp stk' loc' pc' xcp'; n + max_vars e' \<le> length xs; P,Env,h \<turnstile>1 e' : T \<rbrakk>
             \<Longrightarrow> \<exists>e'' xs''. P, e2, n, h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp') \<and> ?red e' xs e'' xs'' e2 pc xcp`
  note bisim2 = `P,e2,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim = `\<And>xs. P,e,n,h \<turnstile> (e, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim1 = `\<And>xs. P,e1,n,h \<turnstile> (e1, xs) \<leftrightarrow> ([], xs, 0, None)`
  note len = `n + max_vars e' \<le> length xs`
  note wt = `P,Env,h \<turnstile>1 e' : T`
  note exec = `?exec (if (e) e1 else e2) stk loc (Suc (Suc (length (compE2 e) + length (compE2 e1) + pc))) xcp stk' loc' pc' xcp'`
  let ?pre = "compE2 e @ IfFalse (2 + int (length (compE2 e1))) # compE2 e1 @ [Goto (1 + int (length (compE2 e2)))]"
  from exec have exec': "exec_meth (compP2 P) (?pre @ compE2 e2)
    ((compxE2 e 0 0 @ compxE2 e1 (Suc (length (compE2 e))) 0) @ shift (length ?pre) (compxE2 e2 0 0))
    h (stk, loc, length ?pre + pc, xcp) ta h' (stk', loc', pc', xcp')"
    by(simp add: shift_compxE2 add_ac exec_move_def)
  hence "?exec e2 stk loc pc xcp stk' loc' (pc' - length ?pre) xcp'"
    unfolding exec_move_def by(rule exec_meth_drop_xt) auto
  from IH[OF this len wt] obtain e'' xs''
    where bisim': "P,e2,n,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc' - length ?pre, xcp')"
    and red: "?red e' xs e'' xs'' e2 pc xcp" by auto
  from bisim' bisim1_bsok[OF bisim] bisim1_bsok[OF bisim1]
  have "P,if (e) e1 else e2,n,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', Suc (Suc (length (compE2 e) + length (compE2 e1) + (pc' - length ?pre))), xcp')"
    by(rule bisim1_bisims1.bisim1CondElse)
  moreover have \<tau>: "\<tau>move2 (if (e) e1 else e2) (Suc (Suc (length (compE2 e) + length (compE2 e1) + pc))) xcp = \<tau>move2 e2 pc xcp"
    by(auto intro: \<tau>move2CondElse)
  moreover from exec' have "pc' \<ge> length ?pre"
    by(rule exec_meth_drop_xt_pc) auto
  moreover hence "Suc (Suc (pc' - Suc (Suc 0))) = pc'" by simp
  ultimately show ?case using red by(fastsimp simp add: nat_number)
next
  case (bisim1CondThrow e n a xs stk loc pc e1 e2)
  note exec = `?exec (if (e) e1 else e2) stk loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  note bisim = `P,e,n,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)`
  from bisim have pc: "pc < length (compE2 e)" by(auto dest: bisim1_ThrowD)
  from bisim have "match_ex_table (compP2 P) (cname_of h a) (0 + pc) (compxE2 e 0 0) = None"
    unfolding compP2_def by(rule  bisim1_xcp_Some_not_caught)
  with exec pc have False
    by(auto elim!: exec_meth.cases simp add: match_ex_table_not_pcs_None exec_move_def)
  thus ?case ..
next
  case (bisim1While1 c n e xs)
  note IH = `\<And>xs stk' loc' pc' xcp' Env T. 
            \<lbrakk> ?exec c [] xs 0 None stk' loc' pc' xcp'; n + max_vars c \<le> length xs; P,Env,h \<turnstile>1 c : T \<rbrakk>
             \<Longrightarrow> \<exists>e'' xs''. P, c, n, h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp') \<and> ?red c xs e'' xs'' c 0 None`
  note bisim = `\<And>xs. P,c,n,h \<turnstile> (c, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim1 = `\<And>xs. P,e,n,h \<turnstile> (e, xs) \<leftrightarrow> ([], xs, 0, None)`
  from `n + max_vars (while (c) e) \<le> length xs`
  have len: "n + max_vars c \<le> length xs" by simp
  from `P,Env,h \<turnstile>1 while (c) e : T` have wt: "P,Env,h \<turnstile>1 c : Boolean" by auto
  note exec = `?exec (while (c) e) [] xs 0 None stk' loc' pc' xcp'`
  let ?post = "IfFalse (int (length (compE2 e)) + 3) # compE2 e @ [Pop, Goto (-2 + (- int (length (compE2 e)) - int (length (compE2 c)))), Push Unit]"
  from exec have "?exec c [] xs 0 None stk' loc' pc' xcp'" by(simp add: exec_move_While1)
  from IH[OF this len wt] obtain e'' xs''
    where bisim': "P,c,n,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp')"
    and red: "?red c xs e'' xs'' c 0 None" by auto
  from bisim' bisim1_bsok[OF bisim1]
  have "P,while (c) e,n,h' \<turnstile> (if (e'') (e;;while(c) e) else unit, xs'') \<leftrightarrow> (stk', loc', pc', xcp')"
    by(rule bisim1While3)
  moreover have "P \<turnstile>1 \<langle>while (c) e, (h, xs)\<rangle> -\<epsilon>\<rightarrow> \<langle>if (c) (e;;while (c) e) else unit, (h, xs)\<rangle>"
    by(rule Red1While)
  hence "\<tau>Red P h (while (c) e) xs (if (c) (e;;while (c) e) else unit) xs"
    by(rule \<tau>Red1step)(rule \<tau>move1WhileRed)
  moreover have "\<tau>move2 (while (c) e) 0 None = \<tau>move2 c 0 None"
    by(auto intro: \<tau>move2While1)
  ultimately show ?case using red by(fastsimp elim!: \<tau>Red_trans intro: Cond1Red)
next
  case (bisim1While3 c n e' xs stk loc pc xcp e)
  note IH = `\<And>stk' loc' pc' xcp' Env T. 
            \<lbrakk> ?exec c stk loc pc xcp stk' loc' pc' xcp'; n + max_vars e' \<le> length xs; P,Env,h \<turnstile>1 e' : T \<rbrakk>
             \<Longrightarrow> \<exists>e'' xs''. P, c, n, h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp') \<and> ?red e' xs e'' xs'' c pc xcp`
  note bisim = ` P,c,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim1 = `\<And>xs. P,e,n,h \<turnstile> (e, xs) \<leftrightarrow> ([], xs, 0, None)`
  from `n + max_vars (if (e') (e;;while (c) e) else unit) \<le> length xs`
  have len: "n + max_vars e' \<le> length xs" by simp
  from `P,Env,h \<turnstile>1 if (e') (e;;while (c) e) else unit : T` have wt: "P,Env,h \<turnstile>1 e' : Boolean" by auto
  note exec = `?exec (while (c) e) stk loc pc xcp stk' loc' pc' xcp'`
  from bisim have pc: "pc \<le> length (compE2 c)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 c)")
    case True
    let ?post = "IfFalse (int (length (compE2 e)) + 3) # compE2 e @ [Pop, Goto (-2 + (- int (length (compE2 e)) - int (length (compE2 c)))), Push Unit]"
    from exec have "exec_meth (compP2 P) (compE2 c @ ?post) (compxE2 c 0 0 @ shift (length (compE2 c)) (compxE2 e (Suc 0) 0)) h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
      by(simp add: shift_compxE2 exec_move_def)
    hence "?exec c stk loc pc xcp stk' loc' pc' xcp'"
      using True unfolding exec_move_def by(rule exec_meth_take_xt)
    from IH[OF this len wt] obtain e'' xs''
      where bisim': "P,c,n,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp')"
      and red: "?red e' xs e'' xs'' c pc xcp" by auto
    from bisim' bisim1_bsok[OF bisim1]
    have "P,while (c) e,n,h' \<turnstile> (if (e'') (e;;while(c) e) else unit, xs'') \<leftrightarrow> (stk', loc', pc', xcp')"
      by(rule bisim1_bisims1.bisim1While3)
    moreover have "\<tau>move2 (while (c) e) pc xcp = \<tau>move2 c pc xcp" using True
      by(auto intro: \<tau>move2While1)
    ultimately show ?thesis using red by(fastsimp elim!: \<tau>Red_trans intro: Cond1Red)
  next
    case False
    with pc have [simp]: "pc = length (compE2 c)" by simp
    with bisim obtain v where stk: "stk = [v]" and xcp: "xcp = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with bisim pc len have red: "\<tau>Red P h e' xs (Val v) loc" by(auto intro: bisim1_Val_\<tau>Red)
    moreover have \<tau>: "\<not> \<tau>move2 (while (c) e) (length (compE2 c)) None"
      by(auto elim: \<tau>move2.cases dest: \<tau>move2_pc_length_compE2)
    moreover have "\<not> \<tau>move1 (if (Val v) (e;;while (c) e) else unit)" by auto
    moreover from bisim1[of loc] bisim1_bsok[OF bisim]
    have "P,while (c) e,n,h \<turnstile> (e;;while(c) e, loc) \<leftrightarrow> ([], loc, Suc (length (compE2 c) + 0), None)"
      by(rule bisim1While4)
    moreover from bisim1_bsok[OF bisim] bisim1_bsok[OF bisim1]
    have "P,while (c) e,n,h \<turnstile> (unit, loc) \<leftrightarrow> ([], loc, Suc (Suc (Suc (length (compE2 c) + length (compE2 e)))), None)"
      by(rule bisim1While7)
    moreover from bisim stk xcp wt have "P,Env,h \<turnstile>1 Val v : Boolean"
      by(auto dest: bisim1_length_compE2_WTrt_eq)
    moreover have "nat (int (length (compE2 c)) + (3 + int (length (compE2 e)))) = Suc (Suc (Suc (length (compE2 c) + length (compE2 e))))" by simp
    ultimately show ?thesis using exec stk xcp
      by(fastsimp elim!: exec_meth.cases intro: Red1CondT Red1CondF simp add: nat_number exec_move_def)
  qed
next
  case (bisim1While4 e n e' xs stk loc pc xcp c)
  note IH = `\<And>stk' loc' pc' xcp' Env T. 
            \<lbrakk> ?exec e stk loc pc xcp stk' loc' pc' xcp'; n + max_vars e' \<le> length xs; P,Env,h \<turnstile>1 e' : T \<rbrakk>
             \<Longrightarrow> \<exists>e'' xs''. P, e, n, h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp') \<and> ?red e' xs e'' xs'' e pc xcp`
  note bisim = `\<And>xs. P,c,n,h \<turnstile> (c, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim1 = `P,e,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  from `n + max_vars (e';; while (c) e) \<le> length xs`
  have len: "n + max_vars e' \<le> length xs" by simp
  from `P,Env,h \<turnstile>1 e';; while (c) e : T` obtain T' where wt: "P,Env,h \<turnstile>1 e' : T'" by auto
  note exec = `?exec (while (c) e) stk loc (Suc (length (compE2 c) + pc)) xcp stk' loc' pc' xcp'`
  from bisim1 have pc: "pc \<le> length (compE2 e)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e)")
    case True
    let ?pre = "compE2 c @ [IfFalse (int (length (compE2 e)) + 3)]"
    let ?post = "[Pop, Goto (-2 + (- int (length (compE2 e)) - int (length (compE2 c)))), Push Unit]"
    from exec have "exec_meth (compP2 P) ((?pre @ compE2 e) @ ?post) (compxE2 c 0 0 @ shift (length ?pre) (compxE2 e 0 0)) h (stk, loc, length ?pre + pc, xcp) ta h' (stk', loc', pc', xcp')"
      by(simp add: shift_compxE2 exec_move_def)
    hence exec': "exec_meth (compP2 P) (?pre @ compE2 e) (compxE2 c 0 0 @ shift (length ?pre) (compxE2 e 0 0)) h (stk, loc, length ?pre + pc, xcp) ta h' (stk', loc', pc', xcp')"
      by(rule exec_meth_take)(simp add: True)
    hence "?exec e stk loc pc xcp stk' loc' (pc' - length ?pre) xcp'"
      unfolding exec_move_def by(rule exec_meth_drop_xt) auto
    from IH[OF this len wt] obtain e'' xs''
      where bisim': "P,e,n,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc' - length ?pre, xcp')"
      and red: "?red e' xs e'' xs'' e pc xcp" by auto
    from red have "?red (e';;while (c) e) xs (e'';;while (c) e) xs'' e pc xcp"
      by(fastsimp intro: Seq1Red)
    moreover from bisim' bisim1_bsok[OF bisim]
    have "P,while (c) e,n,h' \<turnstile> (e'';;while(c) e, xs'') \<leftrightarrow> (stk', loc', Suc (length (compE2 c) + (pc' - length ?pre)), xcp')"
      by(rule bisim1_bisims1.bisim1While4)
    moreover have "\<tau>move2 (while (c) e) (Suc (length (compE2 c) + pc)) xcp = \<tau>move2 e pc xcp" using True
      by(fastsimp intro: \<tau>move2While2 \<tau>move2xcp elim: \<tau>move2.cases dest: \<tau>move2_pc_length_compE2)
    moreover from exec' have "pc' \<ge> length ?pre"
      by(rule exec_meth_drop_xt_pc) auto
    ultimately show ?thesis by fastsimp
  next
    case False
    with pc have [simp]: "pc = length (compE2 e)" by simp
    with bisim1 obtain v where stk: "stk = [v]" and xcp: "xcp = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with bisim1 pc len have red: "\<tau>Red P h e' xs (Val v) loc" by(auto intro: bisim1_Val_\<tau>Red)
    moreover have \<tau>: "\<not> \<tau>move2 (while (c) e) (Suc (length (compE2 c) + length (compE2 e))) None"
      by(fastsimp elim: \<tau>move2.cases dest: \<tau>move2_pc_length_compE2)
    moreover have "\<not> \<tau>move1 (Val v;;while (c) e)" by auto
    moreover from bisim1_bsok[OF bisim] bisim1_bsok[OF bisim1]
    have "P,while (c) e,n,h \<turnstile> (while(c) e, loc) \<leftrightarrow> ([], loc, Suc (Suc (length (compE2 c) + length (compE2 e))), None)"
      by(rule bisim1While6)
    ultimately show ?thesis using exec stk xcp
      by(fastsimp elim!: exec_meth.cases intro: Red1Seq simp add: nat_number exec_move_def)
  qed
next
  case (bisim1While6 c n e xs)
  note bisim1 = `\<And>xs. P,c,n,h \<turnstile> (c, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim2 = `\<And>xs. P,e,n,h \<turnstile> (e, xs) \<leftrightarrow> ([], xs, 0, None)`
  note exec = `?exec (while (c) e) [] xs (Suc (Suc (length (compE2 c) + length (compE2 e)))) None stk' loc' pc' xcp'`
  moreover have "\<tau>move2 (while (c) e) (Suc (Suc (length (compE2 c) + length (compE2 e)))) None"
    by(rule \<tau>move2While3)
  moreover from bisim1_bsok[OF bisim1] bisim1_bsok[OF bisim2] 
  have "P,while (c) e,n,h' \<turnstile> (while (c) e, xs) \<leftrightarrow> ([], xs, 0, None)"
    by(rule bisim1While1)
  ultimately show ?case by(fastsimp elim!: exec_meth.cases intro: \<tau>Red_refl simp add: exec_move_def)
next
  case (bisim1While7 c n e xs)
  note bisim1 = `\<And>xs. P,c,n,h \<turnstile> (c, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim2 = `\<And>xs. P,e,n,h \<turnstile> (e, xs) \<leftrightarrow> ([], xs, 0, None)`
  note exec = `?exec (while (c) e) [] xs (Suc (Suc (Suc (length (compE2 c) + length (compE2 e))))) None stk' loc' pc' xcp'`
  moreover have "\<tau>move2 (while (c) e) (Suc (Suc (Suc (length (compE2 c) + length (compE2 e))))) None"
    by(rule \<tau>move2While4)
  moreover from bisim1_bsok[OF bisim1] bisim1_bsok[OF bisim2]
  have "bsok (while (c) e) n" by simp
  hence "P,while (c) e,n,h' \<turnstile> (unit, xs) \<leftrightarrow> ([Unit], xs, length (compE2 (while (c) e)), None)"
    by(rule bisim1Val2)
  ultimately show ?case by(fastsimp elim!: exec_meth.cases intro: \<tau>Red_refl simp add: exec_move_def)
next
  case (bisim1WhileThrow1 c n a xs stk loc pc e)
  note exec = `?exec (while (c) e) stk loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  note bisim1 = `P,c,n,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)`
  from bisim1 have pc: "pc < length (compE2 c)" by(auto dest: bisim1_ThrowD)
  from bisim1 have "match_ex_table (compP2 P) (cname_of h a) (0 + pc) (compxE2 c 0 0) = None"
    unfolding compP2_def by(rule  bisim1_xcp_Some_not_caught)
  with exec pc have False
    by(auto elim!: exec_meth.cases simp add: match_ex_table_not_pcs_None exec_move_def)
  thus ?case ..
next
  case (bisim1WhileThrow2 e n a xs stk loc pc c)
  note exec = `?exec (while (c) e) stk loc (Suc (length (compE2 c) + pc)) \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  note bisim = `P,e,n,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)`
  from bisim have pc: "pc < length (compE2 e)" by(auto dest: bisim1_ThrowD)
  from bisim have "match_ex_table (compP2 P) (cname_of h a) (0 + pc) (compxE2 e 0 0) = None"
    unfolding compP2_def by(rule  bisim1_xcp_Some_not_caught)
  with exec pc have False
    apply(auto elim!: exec_meth.cases simp add: match_ex_table_not_pcs_None exec_move_def)
    apply(auto dest!: match_ex_table_shift_pcD simp only: compxE2_size_convs)
    apply simp
    done
  thus ?case ..
next
  case (bisim1Throw1 e n e' xs stk loc pc xcp)
  note IH = `\<And>stk' loc' pc' xcp' Env T. 
            \<lbrakk> ?exec e stk loc pc xcp stk' loc' pc' xcp'; n + max_vars e' \<le> length xs; P,Env,h \<turnstile>1 e' : T \<rbrakk>
             \<Longrightarrow> \<exists>e'' xs''. P, e, n, h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp') \<and> ?red e' xs e'' xs'' e pc xcp`
  note exec = `?exec (throw e) stk loc pc xcp stk' loc' pc' xcp'`
  note bisim = `P,e,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note len = `n + max_vars (throw e') \<le> length xs`
  from `P,Env,h \<turnstile>1 throw e' : T` obtain T' where wt: "P,Env,h \<turnstile>1 e' : T'"
    and T': "P \<turnstile> T' \<le> Class Throwable" by auto
  from bisim have pc: "pc \<le> length (compE2 e)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e)")
    case True
    with exec have exec': "?exec e stk loc pc xcp stk' loc' pc' xcp'" by(simp add: exec_move_Throw)
    from True have "\<tau>move2 (throw e) pc xcp = \<tau>move2 e pc xcp" by(auto intro: \<tau>move2Throw1)
    with IH[OF exec' _ wt] len show ?thesis
      by(fastsimp intro: bisim1_bisims1.bisim1Throw1 Throw1Red)
  next
    case False
    with pc have [simp]: "pc = length (compE2 e)" by simp
    with bisim obtain v where stk: "stk = [v]" and xcp: "xcp = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with bisim pc len have red: "\<tau>Red P h e' xs (Val v) loc" by(auto intro: bisim1_Val_\<tau>Red)
    hence "\<tau>Red P h (throw e') xs (throw (Val v)) loc" by auto
    moreover have \<tau>: "\<tau>move2 (throw e) pc None" by(auto intro: \<tau>move2Throw2)
    moreover from bisim1_bsok[OF bisim]
    have "\<And>a. P,throw e,n,h \<turnstile> (Throw a, loc) \<leftrightarrow> ([Addr a], loc, length (compE2 e), \<lfloor>a\<rfloor>)"
      by(rule bisim1Throw2)
    moreover from bisim1_bsok[OF bisim]
    have "P,throw e,n,h \<turnstile> (THROW NullPointer, loc) \<leftrightarrow> ([Null], loc, length (compE2 e), \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>)"
      by(rule bisim1ThrowNull)
    moreover from bisim stk xcp wt have "P,Env,h \<turnstile>1 Val v : T'"
      by(auto dest: bisim1_length_compE2_WTrt_eq)
    moreover with T' have "v \<noteq> Null \<Longrightarrow> \<exists>C. T' = Class C" by(cases T')(auto dest: Array_widen)
    moreover have "\<tau>Red P h (throw null) loc (THROW NullPointer) loc"
      by(rule \<tau>Red1step[OF Red1ThrowNull])(rule \<tau>move1ThrowNull)
    ultimately show ?thesis using exec stk xcp T' unfolding exec_move_def
      by(fastsimp elim!: exec_meth.cases intro: \<tau>Red_refl elim: \<tau>Red_trans)
  qed
next
  case (bisim1Throw2 e n a xs)
  note exec = `?exec (throw e) [Addr a] xs (length (compE2 e)) \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  hence False by(auto elim!: exec_meth.cases dest: match_ex_table_pc_length_compE2 simp add: exec_move_def)
  thus ?case ..
next
  case (bisim1ThrowNull e n xs)
  note exec = `?exec (throw e) [Null] xs (length (compE2 e)) \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor> stk' loc' pc' xcp'`
  hence False by(auto elim!: exec_meth.cases dest: match_ex_table_pc_length_compE2 simp add: exec_move_def)
  thus ?case ..
next
  case (bisim1ThrowThrow e n a xs stk loc pc)
  note exec = `?exec (throw e) stk loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'`
  note bisim1 = `P,e,n,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)`
  from bisim1 have pc: "pc < length (compE2 e)" by(auto dest: bisim1_ThrowD)
  from bisim1 have "match_ex_table (compP2 P) (cname_of h a) (0 + pc) (compxE2 e 0 0) = None"
    unfolding compP2_def by(rule  bisim1_xcp_Some_not_caught)
  with exec pc have False by(auto elim!: exec_meth.cases simp add: exec_move_def)
  thus ?case ..
next
  case (bisim1Try e V e' xs stk loc pc xcp e2 C')
  note IH = `\<And>stk' loc' pc' xcp' Env T. 
            \<lbrakk> ?exec e stk loc pc xcp stk' loc' pc' xcp'; V + max_vars e' \<le> length xs; P,Env,h \<turnstile>1 e' : T \<rbrakk>
             \<Longrightarrow> \<exists>e'' xs''. P, e, V, h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp') \<and> ?red e' xs e'' xs'' e pc xcp`
  note bisim = ` P,e,V,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim1 = `\<And>xs. P,e2,Suc V,h \<turnstile> (e2, xs) \<leftrightarrow> ([], xs, 0, None)`
  note exec = `?exec (try e catch(C' V) e2) stk loc pc xcp stk' loc' pc' xcp'`
  from `V + max_vars (try e' catch(C' V) e2) \<le> length xs`
  have len: "V + max_vars e' \<le> length xs" and V: "V < length xs" by simp_all
  from `P,Env,h \<turnstile>1 try e' catch(C' V) e2 : T` obtain T'
    where wt: "P,Env,h \<turnstile>1 e' : T'" by auto
  from bisim have pc: "pc \<le> length (compE2 e)" by(rule bisim1_pc_length_compE2)
  show ?case
  proof(cases "pc < length (compE2 e)")
    case True
    note pc = True
    show ?thesis
    proof(cases "xcp = None \<or> (\<exists>a'. xcp = \<lfloor>a'\<rfloor> \<and> match_ex_table (compP2 P) (cname_of h a') pc (compxE2 e 0 0) \<noteq> None)")
      case False
      then obtain a' where Some: "xcp = \<lfloor>a'\<rfloor>" 
	and True: "match_ex_table (compP2 P) (cname_of h a') pc (compxE2 e 0 0) = None" by(auto simp del: not_None_eq)
      from Some bisim wt have "\<exists>C. typeof\<^bsub>h\<^esub> (Addr a') = \<lfloor>Class C\<rfloor> \<and> P \<turnstile> C \<preceq>\<^sup>* Throwable"
	by -(rule bisim1_WTrt1_Throw_ObjD, auto)
      then obtain C'' fs where ha': "h a' = \<lfloor>Obj C'' fs\<rfloor>" 
	and subclsThrow: "P \<turnstile> C'' \<preceq>\<^sup>* Throwable" by(auto split: heapobj.split_asm)
      with exec True Some pc have subcls: "P \<turnstile> C'' \<preceq>\<^sup>* C'"
	apply(auto elim!: exec_meth.cases simp add: match_ex_table_append compP2_def matches_ex_entry_def exec_move_def split: split_if_asm)
	apply(simp only: compxE2_size_convs)
	apply simp
	done
      moreover from ha' subclsThrow have red: "\<tau>Red P h e' xs (Throw a') loc"
	and bisim': "P,e,V,h \<turnstile> (Throw a', loc) \<leftrightarrow> (stk, loc, pc, \<lfloor>a'\<rfloor>)" using bisim True len
	unfolding Some compP2_def by(blast dest: bisim1_xcp_\<tau>Red)+
      from red have lenloc: "length loc = length xs" by(rule \<tau>Red_preserves_len)
      from red have "\<tau>Red P h (try e' catch(C' V) e2) xs (try (Throw a') catch(C' V) e2) loc" by auto
      hence "\<tau>Red P h (try e' catch(C' V) e2) xs {V:Class C'=None; e2}\<^bsub>False\<^esub> (loc[V := Addr a'])"
	using ha' subcls V unfolding lenloc[symmetric]
	by(rule \<tau>Red_step[OF _ Red1TryCatch])(rule \<tau>move1TryFail)
      moreover from pc have "\<tau>move2 (try e catch(C' V) e2) pc \<lfloor>a'\<rfloor>" by(auto intro: \<tau>move2xcp)
      moreover from bisim' ha' subcls bisim1_bsok[OF bisim1]
      have "P,try e catch(C' V) e2,V,h \<turnstile> ({V:Class C'=None; e2}\<^bsub>False\<^esub>, loc[V := Addr a']) \<leftrightarrow> ([Addr a'], loc, Suc (length (compE2 e)), None)"
	by(rule bisim1TryCatch1)
      ultimately show ?thesis using exec True pc Some ha' subclsThrow
	apply(auto elim!: exec_meth.cases simp add: add_ac nat_number match_ex_table_append matches_ex_entry_def compP2_def exec_move_def)
	apply fastsimp
	apply(simp only: compxE2_size_convs, auto dest: match_ex_table_shift_pcD)
	done
    next
      case True
      let ?post = "Goto (int (length (compE2 e2)) + 2) # Store V # compE2 e2"
      from exec True have "exec_meth (compP2 P) (compE2 e @ ?post) (compxE2 e 0 0 @ shift (length (compE2 e)) (compxE2 e2 (Suc (Suc 0)) 0)) h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
	by(auto elim!: exec_meth.cases intro: exec_meth.intros simp add: match_ex_table_append shift_compxE2 exec_move_def)
      hence "?exec e stk loc pc xcp stk' loc' pc' xcp'"
	using pc unfolding exec_move_def by(rule exec_meth_take_xt)
      from IH[OF this len wt] obtain e'' xs''
	where bisim': "P,e,V,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp')"
	and red': "?red e' xs e'' xs'' e pc xcp" by auto
      from bisim' bisim1_bsok[OF bisim1]
      have "P,try e catch(C' V) e2,V,h' \<turnstile> (try e'' catch(C' V) e2, xs'') \<leftrightarrow> (stk', loc', pc', xcp')"
	by(rule bisim1_bisims1.bisim1Try)
      moreover from pc have "\<tau>move2 (try e catch(C' V) e2) pc xcp = \<tau>move2 e pc xcp"
	by(auto intro: \<tau>move2Try1)
      ultimately show ?thesis using red' by(fastsimp intro: Try1Red)
    qed
  next
    case False
    with pc have [simp]: "pc = length (compE2 e)" by simp
    with bisim obtain v where stk: "stk = [v]" and xcp: "xcp = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with bisim pc len have red: "\<tau>Red P h e' xs (Val v) loc" by(auto intro: bisim1_Val_\<tau>Red)
    hence "\<tau>Red P h (try e' catch(C' V) e2) xs (try (Val v) catch(C' V) e2) loc" by auto
    hence "\<tau>Red P h (try e' catch(C' V) e2) xs (Val v) loc"
      by(rule \<tau>Red_step)(rule Red1Try \<tau>move1TryRed)+
    moreover have \<tau>: "\<tau>move2 (try e catch(C' V) e2) pc None" by(auto intro: \<tau>move2TryJump)
    moreover from bisim1_bsok[OF bisim] bisim1_bsok[OF bisim1]
    have "bsok (try e catch(C' V) e2) V" by simp
    hence "P,try e catch(C' V) e2,V,h \<turnstile> (Val v, loc) \<leftrightarrow> ([v], loc, length (compE2 (try e catch(C' V) e2)), None)"
      by(rule bisim1Val2)
    moreover have "nat (int (length (compE2 e)) + (int (length (compE2 e2)) + 2)) = length (compE2 (try e catch(C' V) e2))" by simp
    ultimately show ?thesis using exec stk xcp
      by(fastsimp elim!: exec_meth.cases simp add: exec_move_def)
  qed
next
  case (bisim1TryCatch1 e V a xs stk loc pc C'' fs C' e2)
  note exec = `?exec (try e catch(C' V) e2) [Addr a] loc (Suc (length (compE2 e))) None stk' loc' pc' xcp'`
  note bisim2 = `P,e2,Suc V,h \<turnstile> (e2, loc[V := Addr a]) \<leftrightarrow> ([], loc[V := Addr a], 0, None)`
  note bisim1 = `P,e,V,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)`
  hence [simp]: "xs = loc" by(auto dest: bisim1_ThrowD)
  from bisim2 bisim1_bsok[OF bisim1]
  have "P, try e catch(C' V) e2, V, h \<turnstile> ({V:Class C'=None; e2}\<^bsub>False\<^esub>, loc[V := Addr a]) \<leftrightarrow> ([], loc[V := Addr a], Suc (Suc (length (compE2 e) + 0)), None)"
    by(rule bisim1TryCatch2)
  moreover have "\<tau>move2 (try e catch(C' V) e2) (Suc (length (compE2 e))) None"
    by(rule \<tau>move2TryCatch2)
  ultimately show ?case using exec by(fastsimp elim!: exec_meth.cases intro: \<tau>Red_refl simp add: exec_move_def)
next
  case (bisim1TryCatch2 e2 V e' xs stk loc pc xcp e C')
  note IH = `\<And>stk' loc' pc' xcp' Env T. 
            \<lbrakk> ?exec e2 stk loc pc xcp stk' loc' pc' xcp'; Suc V + max_vars e' \<le> length xs; P,Env,h \<turnstile>1 e' : T \<rbrakk>
             \<Longrightarrow> \<exists>e'' xs''. P, e2, Suc V, h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp') \<and> ?red e' xs e'' xs'' e2 pc xcp`
  note bisim2 = `P,e2,Suc V,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim = `\<And>xs. P,e,V,h \<turnstile> (e, xs) \<leftrightarrow> ([], xs, 0, None)`
  note exec = `?exec (try e catch(C' V) e2) stk loc (Suc (Suc (length (compE2 e) + pc))) xcp stk' loc' pc' xcp'`
  from `V + max_vars {V:Class C'=None; e'}\<^bsub>False\<^esub> \<le> length xs`
  have len: "Suc V + max_vars e' \<le> length xs" and V: "V < length xs" by simp_all
  from `P,Env,h \<turnstile>1 {V:Class C'=None; e'}\<^bsub>False\<^esub> : T` have wt: "P,Env@[Class C'],h \<turnstile>1 e' : T" by auto
  let ?pre = "compE2 e @ [Goto (int (length (compE2 e2)) + 2), Store V]"
  from exec have "exec_meth (compP2 P) (?pre @ compE2 e2)
     (compxE2 e 0 0 @ shift (length ?pre) (compxE2 e2 0 0) @ [(0, length (compE2 e), C', Suc (length (compE2 e)), 0)])
     h (stk, loc, length ?pre + pc, xcp) ta h' (stk', loc', pc', xcp')"
    by(simp add: shift_compxE2 exec_move_def)
  hence exec': "exec_meth (compP2 P) (?pre @ compE2 e2) (compxE2 e 0 0 @ shift (length ?pre) (compxE2 e2 0 0))
     h (stk, loc, length ?pre + pc, xcp) ta h' (stk', loc', pc', xcp')"
    by(auto elim!: exec_meth.cases intro: exec_meth.intros simp add: match_ex_table_append matches_ex_entry_def)
  hence "?exec e2 stk loc pc xcp stk' loc' (pc' - length ?pre) xcp'"
    unfolding exec_move_def by(rule exec_meth_drop_xt) auto
  from IH[OF this len wt] obtain e'' xs''
    where bisim': "P,e2,Suc V,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc' - length ?pre, xcp')"
    and red: "?red e' xs e'' xs'' e2 pc xcp" by auto
  from red have "length xs'' = length xs" by(auto dest!: \<tau>Red_preserves_len red1_preserves_len split: split_if_asm)
  with red V have "?red {V:Class C'=None; e'}\<^bsub>False\<^esub> xs {V:Class C'=None; e''}\<^bsub>False\<^esub> xs'' e2 pc xcp"
    apply(auto)
    apply(frule \<tau>Red_preserves_len)
    apply(fastsimp intro: Block1RedNone)
    done
  moreover
  from bisim' bisim1_bsok[OF bisim]
  have "P,try e catch(C' V) e2,V,h' \<turnstile> ({V:Class C'=None;e''}\<^bsub>False\<^esub>, xs'') \<leftrightarrow> (stk', loc', Suc (Suc (length (compE2 e) + (pc' - length ?pre))), xcp')"
    by(rule bisim1_bisims1.bisim1TryCatch2)
  moreover have "\<tau>move2 (try e catch(C' V) e2) (Suc (Suc (length (compE2 e) + pc))) xcp = \<tau>move2 e2 pc xcp"
    by(fastsimp intro: \<tau>move2xcp \<tau>move2Try2 \<tau>move2BlockNone elim: \<tau>move2.cases dest: \<tau>move2_pc_length_compE2)
  moreover from exec' have "pc' \<ge> length ?pre"
    by(rule exec_meth_drop_xt_pc) auto
  moreover hence "Suc (Suc (pc' - Suc (Suc 0))) = pc'" by simp
  ultimately show ?case using red V by(fastsimp simp add: nat_number)
next
  case (bisim1TryFail e V a xs stk loc pc C'' fs C' e2)
  note bisim = `P,e,V,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)`
  from bisim have pc: "pc < length (compE2 e)" by(auto dest: bisim1_ThrowD)
  from bisim have "match_ex_table (compP2 P) (cname_of h a) (0 + pc) (compxE2 e 0 0) = None"
    unfolding compP2_def by(rule  bisim1_xcp_Some_not_caught)
  with `?exec (try e catch(C' V) e2) stk loc pc \<lfloor>a\<rfloor> stk' loc' pc' xcp'` pc `h a = \<lfloor>Obj C'' fs\<rfloor>` `\<not> P \<turnstile> C'' \<preceq>\<^sup>* C'`
  have False by(auto elim!: exec_meth.cases simp add: matches_ex_entry_def compP2_def match_ex_table_append_not_pcs exec_move_def)
  thus ?case ..
next
  case (bisim1TryCatchThrow e2 V a xs stk loc pc e C')
  note bisim = `P,e2,Suc V,h \<turnstile> (Throw a, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>)`
  from bisim have pc: "pc < length (compE2 e2)" by(auto dest: bisim1_ThrowD)
  from bisim have "match_ex_table (compP2 P) (cname_of h a) (0 + pc) (compxE2 e2 0 0) = None"
    unfolding compP2_def by(rule  bisim1_xcp_Some_not_caught)
  with `?exec (try e catch(C' V) e2) stk loc (Suc (Suc (length (compE2 e) + pc))) \<lfloor>a\<rfloor> stk' loc' pc' xcp'` pc
  have False apply(auto elim!: exec_meth.cases simp add: compxE2_size_convs match_ex_table_append_not_pcs exec_move_def)
    apply(auto dest!: match_ex_table_shift_pcD simp add: match_ex_table_append matches_ex_entry_def compP2_def)
    done
  thus ?case ..
next
  case bisims1Nil
  hence False by(auto elim!: exec_meth.cases simp add: exec_moves_def)
  thus ?case ..
next
  case (bisims1List1 e n e' xs stk loc pc xcp es)
  note IH1 = `\<And>stk' loc' pc' xcp' Env T. 
             \<lbrakk> ?exec e stk loc pc xcp stk' loc' pc' xcp'; n + max_vars e' \<le> length xs; P,Env,h \<turnstile>1 e' : T \<rbrakk>
             \<Longrightarrow> \<exists>e'' xs''. P, e, n, h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp') \<and> ?red e' xs e'' xs'' e pc xcp`
  note IH2 = `\<And>xs stk' loc' pc' xcp' Env Ts. 
             \<lbrakk> ?execs es [] xs 0 None stk' loc' pc' xcp'; n + max_varss es \<le> length xs; P,Env,h \<turnstile>1 es [:] Ts \<rbrakk>
             \<Longrightarrow> \<exists>es'' xs''. P, es, n, h' \<turnstile> (es'', xs'') [\<leftrightarrow>] (stk', loc', pc', xcp') \<and> ?reds es xs es'' xs'' es 0 None`
  note exec = `?execs (e # es) stk loc pc xcp stk' loc' pc' xcp'`
  note bisim1 = `P,e,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note bisim2 = `P,es,n,h \<turnstile> (es, loc) [\<leftrightarrow>] ([], loc, 0, None)`
  note len = `n + max_varss (e' # es) \<le> length xs`
  note wt = `P,Env,h \<turnstile>1 e' # es [:] Ts`
  then obtain T' Ts' where wt1: "P,Env,h \<turnstile>1 e' : T'" and wt2: "P,Env,h \<turnstile>1 es [:] Ts'" by auto
  from bisim1 have pc: "pc \<le> length (compE2 e)" by(rule bisim1_pc_length_compE2)
  from bisim1 have lenxs: "length xs = length loc" by(rule bisim1_length_xs)
  show ?case
  proof(cases "pc < length (compE2 e)")
    case True
    with exec have exec': "?exec e stk loc pc xcp stk' loc' pc' xcp'"
      by(auto simp add: compxEs2_size_convs exec_moves_def exec_move_def intro: exec_meth_take_xt)
    from True have "\<tau>moves2 (e # es) pc xcp = \<tau>move2 e pc xcp"
      by(auto intro: \<tau>moves2Hd elim!: \<tau>moves2.cases)
    with IH1[OF exec' _ wt1] bisims1_bsoks[OF bisim2] len show ?thesis
      by(fastsimp intro: bisim1_bisims1.bisims1List1 \<tau>Red_inj_\<tau>Reds List1Red1)
  next
    case False
    with pc have pc [simp]: "pc = length (compE2 e)" by simp
    with bisim1 obtain v where stk: "stk = [v]" and xcp: "xcp = None"
      by(auto dest: bisim1_pc_length_compE2D)
    with bisim1 pc len have red: "\<tau>Red P h e' xs (Val v) loc" by(auto intro: bisim1_Val_\<tau>Red)
    hence "\<tau>Reds P h (e' # es) xs (Val v # es) loc" by(rule \<tau>Red_inj_\<tau>Reds)
    moreover from exec stk xcp
    have exec': "exec_meth (compP2 P) (compE2 e @ compEs2 es) (compxE2 e 0 0 @ shift (length (compE2 e)) (stack_xlift (length [v]) (compxEs2 es 0 0))) h ([] @ [v], loc, length (compE2 e) + 0, None) ta h' (stk', loc', pc', xcp')"
      by(simp add: shift_compxEs2 stack_xlift_compxEs2 exec_moves_def)
    hence "exec_meth (compP2 P) (compEs2 es) (stack_xlift (length [v]) (compxEs2 es 0 0)) h ([] @ [v], loc, 0, None) ta h' (stk', loc', pc' - length (compE2 e), xcp')"
      by(rule exec_meth_drop_xt) auto
    with bisim2 obtain stk'' where stk': "stk' = stk'' @ [v]"
      and exec'': "exec_moves P es h ([], loc, 0, None) ta h' (stk'', loc', pc' - length (compE2 e), xcp')"
      by(unfold exec_moves_def)(drule (1) exec_meth_stk_splits, auto)
    from IH2[OF exec'' _ wt2] len lenxs obtain es'' xs''
      where bisim': "P,es,n,h' \<turnstile> (es'', xs'') [\<leftrightarrow>] (stk'', loc', pc' - length (compE2 e), xcp')"
      and red': "?reds es loc es'' xs'' es 0 None" by auto
    from bisim' bisim1 have "P,e # es,n,h' \<turnstile> (Val v # es'', xs'') [\<leftrightarrow>] (stk'' @ [v], loc', length (compE2 e) + (pc' - length (compE2 e)), xcp')"
      by(rule bisims1List2[OF _ bisim1_bsok])
    moreover have "\<tau>moves2 (e # es) (length (compE2 e)) None = \<tau>moves2 es 0 None"
      by(auto dest: \<tau>moves2Tl \<tau>move2_pc_length_compE2 elim: \<tau>moves2.cases)
    moreover from exec' have "pc' \<ge> length (compE2 e)"
      by(rule exec_meth_drop_xt_pc) auto
    ultimately show ?thesis using red' xcp stk stk'
      apply auto
      apply(fastsimp intro: \<tau>Reds_trans \<tau>Reds_cons_\<tau>Reds)
      apply(rule exI conjI|erule \<tau>Reds_trans \<tau>Reds_cons_\<tau>Reds List1Red2|assumption)+
      by auto
  qed
next
  case (bisims1List2 es n es' xs stk loc pc xcp e v)
  note IH = `\<And>stk' loc' pc' xcp' Env Ts. 
             \<lbrakk> ?execs es stk loc pc xcp stk' loc' pc' xcp'; n + max_varss es' \<le> length xs; P,Env,h \<turnstile>1 es' [:] Ts \<rbrakk>
             \<Longrightarrow> \<exists>es'' xs''. P, es, n, h' \<turnstile> (es'', xs'') [\<leftrightarrow>] (stk', loc', pc', xcp') \<and> ?reds es' xs es'' xs'' es pc xcp`
  note exec = `?execs (e # es) (stk @ [v]) loc (length (compE2 e) + pc) xcp stk' loc' pc' xcp'`
  note bisim1 = `P,e,n,h \<turnstile> (e, xs) \<leftrightarrow> ([], xs, 0, None)`
  note bisim2 = `P,es,n,h \<turnstile> (es', xs) [\<leftrightarrow>] (stk, loc, pc, xcp)`
  note len = `n + max_varss (Val v # es') \<le> length xs`
  note wt = `P,Env,h \<turnstile>1 Val v # es' [:] Ts`
  then obtain Ts' where wt2: "P,Env,h \<turnstile>1 es' [:] Ts'" by auto
  from exec have exec': "exec_meth (compP2 P) (compE2 e @ compEs2 es) (compxE2 e 0 0 @ shift (length (compE2 e)) (stack_xlift (length [v]) (compxEs2 es 0 0))) h (stk @ [v], loc, length (compE2 e) + pc, xcp) ta h' (stk', loc', pc', xcp')"
    by(simp add: shift_compxEs2 stack_xlift_compxEs2 exec_moves_def)
  hence "exec_meth (compP2 P) (compEs2 es) (stack_xlift (length [v]) (compxEs2 es 0 0)) h (stk @ [v], loc, pc, xcp) ta h' (stk', loc', pc' - length (compE2 e), xcp')"
    by(rule exec_meth_drop_xt) auto
  with bisim2 obtain stk'' where stk': "stk' = stk'' @ [v]"
    and exec'': "exec_moves P es h (stk, loc, pc, xcp) ta h' (stk'', loc', pc' - length (compE2 e), xcp')"
    by(unfold exec_moves_def)(drule (1) exec_meth_stk_splits, auto)
  from IH[OF exec'' _ wt2] len obtain es'' xs''
    where bisim': "P,es,n,h' \<turnstile> (es'', xs'') [\<leftrightarrow>] (stk'', loc', pc' - length (compE2 e), xcp')"
    and red': "?reds es' xs es'' xs'' es pc xcp" by auto
  from bisim' bisim1 have "P,e # es,n,h' \<turnstile> (Val v # es'', xs'') [\<leftrightarrow>] (stk'' @ [v], loc', length (compE2 e) + (pc' - length (compE2 e)), xcp')"
    by(rule bisim1_bisims1.bisims1List2[OF _ bisim1_bsok])
  moreover have "\<tau>moves2 (e # es) (length (compE2 e) + pc) xcp = \<tau>moves2 es pc xcp"
    by(auto dest: \<tau>moves2Tl \<tau>move2_pc_length_compE2 elim: \<tau>moves2.cases)
  moreover from exec' have "pc' \<ge> length (compE2 e)"
    by(rule exec_meth_drop_xt_pc) auto
  ultimately show ?case using red' stk'
    apply auto
    apply(fastsimp intro: \<tau>Reds_trans \<tau>Reds_cons_\<tau>Reds)
    apply(rule exI conjI|erule \<tau>Reds_trans \<tau>Reds_cons_\<tau>Reds List1Red2|assumption)+
    by auto
qed

lemma bisim1_xcpD: "P,e,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>) \<Longrightarrow> pc < length (compE2 e)"
  and bisims1_xcpD: "P,es,n,h \<turnstile> (es', xs) [\<leftrightarrow>] (stk, loc, pc, \<lfloor>a\<rfloor>) \<Longrightarrow> pc < length (compEs2 es)"
apply(induct e n e' xs stk loc pc xcp\<equiv>"\<lfloor>a::addr\<rfloor>" and es n es' xs stk loc pc xcp\<equiv>"\<lfloor>a:: addr\<rfloor>" rule: bisim1_bisims1_inducts_split)
apply(simp_all)
done

lemma bisim1_match_Some_stk_length:
  "\<lbrakk> P,E,n,h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, \<lfloor>a\<rfloor>);
     match_ex_table (compP2 P) (cname_of h a) pc (compxE2 E 0 0) = \<lfloor>(pc', d)\<rfloor> \<rbrakk>
  \<Longrightarrow> d \<le> length stk"

  and bisims1_match_Some_stk_length:
  "\<lbrakk> P,Es,n,h \<turnstile> (es, xs) [\<leftrightarrow>] (stk, loc, pc, \<lfloor>a\<rfloor>);
     match_ex_table (compP2 P) (cname_of h a) pc (compxEs2 Es 0 0) = \<lfloor>(pc', d)\<rfloor> \<rbrakk>
  \<Longrightarrow> d \<le> length stk"
proof(induct E n e xs stk loc pc xcp\<equiv>"\<lfloor>a::addr\<rfloor>" and Es n es xs stk loc pc xcp\<equiv>"\<lfloor>a::addr\<rfloor>"
      arbitrary: pc' d and pc' d rule: bisim1_bisims1_inducts_split)
  case bisim1Call1 thus ?case
    by(fastsimp dest: bisim1_xcpD simp add: match_ex_table_append match_ex_table_not_pcs_None)
next
  case bisim1CallThrowObj thus ?case
    by(fastsimp dest: bisim1_xcpD simp add: match_ex_table_append match_ex_table_not_pcs_None)
next
  case bisim1Sync4 thus ?case
    apply(clarsimp simp add: match_ex_table_not_pcs_None match_ex_table_append matches_ex_entry_def split: split_if_asm)
    apply(fastsimp simp add: match_ex_table_compxE2_shift_conv dest: bisim1_xcpD)
    done
next
  case bisim1Try thus ?case
    by(fastsimp simp add: match_ex_table_append matches_ex_entry_def match_ex_table_not_pcs_None dest: bisim1_xcpD split: split_if_asm)
next
  case bisim1TryCatch2 thus ?case
    apply(clarsimp simp add: match_ex_table_not_pcs_None match_ex_table_append matches_ex_entry_def split: split_if_asm)
    apply(fastsimp simp add: match_ex_table_compxE2_shift_conv dest: bisim1_xcpD)
    done
next
  case bisim1TryFail thus ?case
    by(fastsimp simp add: match_ex_table_append matches_ex_entry_def match_ex_table_not_pcs_None dest: bisim1_xcpD split: split_if_asm)
next
  case bisim1TryCatchThrow thus ?case
    apply(clarsimp simp add: match_ex_table_not_pcs_None match_ex_table_append matches_ex_entry_def split: split_if_asm)
    apply(fastsimp simp add: match_ex_table_compxE2_shift_conv dest: bisim1_xcpD)
    done
next
  case bisims1List1 thus ?case
    by(fastsimp simp add: match_ex_table_append split: split_if_asm dest: bisim1_xcpD match_ex_table_pcsD)
qed(fastsimp simp add: match_ex_table_not_pcs_None match_ex_table_append match_ex_table_compxE2_shift_conv match_ex_table_compxEs2_shift_conv match_ex_table_compxE2_stack_conv match_ex_table_compxEs2_stack_conv matches_ex_entry_def dest: bisim1_xcpD)+

lemma \<tau>Red_simulates_exec_instr_aux1:
  assumes wf: "wf_J1_prog P"
  and \<tau>: "\<tau>Move2 P (None, h, (stk, loc, C, M, pc) # FRS)"
  and exec: "(ta, xcp', h', frs') \<in> set (exec_instr ((compE2 body @ [Return]) ! pc) (compP2 P) h stk loc C M pc FRS)"
  and pc: "pc < Suc (length (compE2 body))"
  and chk: "check_instr ((compE2 body @ [Return]) ! pc) (compP2 P) h stk loc C M pc FRS"
  and bl: "bisim1_list P h C M (length Ts) exs FRS"
  and sees: "P \<turnstile> C sees M: Ts\<rightarrow>T = body in D"
  and bisim: "P,blocks1 (Suc 0) Ts body,Suc 0,h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, None)"
  and exsconf: "exsconf P h T (e, xs)"
  and hconf: "P \<turnstile> h \<surd>"
  shows "h = h' \<and> (\<exists>e' xs' exs'. \<tau>Red1 P h ((e, xs), exs) ((e', xs'), exs') \<and> bisim1_list1 P h (e', xs') exs' xcp' frs')"
proof -
  from exsconf have len': "Suc 0 + max_vars e \<le> length xs" by(auto elim: exsconf.cases)
  have True: "length frs' = Suc (length FRS)"
  proof(rule ccontr)
    assume "length frs' \<noteq> Suc (length FRS)"
    with exec sees pc compE2_not_Return[of body]
    have "pc = length (compE2 body) \<or> (\<exists>M n. compE2 body ! pc = Invoke M n)"
      apply(cases "compE2 body ! pc")
      apply(auto split: split_if_asm simp add: split_beta compP2_def compMb2_def)
      apply(metis in_set_conv_nth)+
      done
    thus False
    proof
      assume "pc = length (compE2 body)"
      with \<tau> sees show False by(auto dest: \<tau>move2_pc_length_compE2)
    next
      assume "\<exists>M n. compE2 body ! pc = Invoke M n"
      with \<tau> sees pc show False by(auto dest: \<tau>move2_compE2_not_Invoke simp: compP2_def compMb2_def)
    qed
  qed

  with exec have "\<exists>stk' loc' pc'. frs' = (stk', loc', C, M, pc') # FRS"
    by(cases "(compE2 body @ [Return]) ! pc")(auto split: split_if_asm sum.splits)
  then obtain stk' loc' pc' where [simp]: "frs' = (stk', loc', C, M, pc') # FRS" by blast
  from exec sees True pc chk
  have exec': "exec_move P (blocks1 (Suc 0) Ts body) h (stk, loc, pc, None) ta h' (stk', loc', pc', xcp')"
    apply(simp add: compP2_def compMb2_def exec_move_def split: split_if_asm)
    apply(rule exec_instr)
      apply(cases "compE2 body ! pc", auto simp add: split_beta neq_Nil_conv split: split_if_asm)
      apply(force split: sum.split_asm)
     apply(force split: sum.split_asm)
    apply(cases "compE2 body ! pc", auto simp add: split_beta neq_Nil_conv split: split_if_asm)
    done
  from exec' have "pc < length (compE2 body)" by(auto simp add: exec_move_def)
  with \<tau> sees have \<tau>: "\<tau>move2 body pc None" by(auto simp add: compP2_def compMb2_def)
  with exec' have h' [simp]: "h' = h"
    by(auto elim: exec_meth.cases intro: exec_meth_\<tau>_heap_unchanged simp add: exec_move_def)
  from \<tau> red1_simulates_exec_instr[OF wf hconf bisim, simplified, OF exec'] len' exsconf
  obtain e'' xs'' where bisim': "P,blocks1 (Suc 0) Ts body,Suc 0,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp')"
    and red: "\<tau>Red P h e xs e'' xs''" by(fastsimp elim!: exsconf.cases)
  from red have Red: "\<tau>Red1 P h ((e, xs), exs) ((e'', xs''), exs)" by(rule \<tau>Red_into_\<tau>Red1)
  moreover from bl sees bisim' have "bisim1_list1 P h (e'', xs'') exs xcp' ((stk', loc', C, M, pc') # FRS)"
    unfolding h' using \<tau>Red1_preserves_sconf[OF wf hconf exsconf red] hconf by(rule bisim1_list1.bl1_Normal)
  ultimately show ?thesis by auto
qed

lemma \<tau>Red1_simulates_exec_1_\<tau>:
  assumes wf: "wf_J1_prog P"
  and exec: "exec_1' (compP2 P) (xcp, h, frs) ta (xcp', h', frs')"
  and bisim: "bisim1_list1 P h (e, xs) exs xcp frs"
  and \<tau>: "\<tau>Move2 P (xcp, h, frs)"
  shows "h = h' \<and> (\<exists>e' xs' exs'. \<tau>Red1 P h ((e, xs), exs) ((e', xs'), exs') \<and> bisim1_list1 P h (e', xs') exs' xcp' frs')"
using exec
proof(cases)
  case (exec_1_Normal TA XCP' H' FRS' C M pc H stk loc FRS)
  hence [simp]: "xcp = None" "H = h" "frs = (stk, loc, C, M, pc) # FRS" "TA = ta" "XCP' = xcp'" "H' = h'" "FRS' = frs'"
    by(simp_all)
  note exec = `(TA, XCP', H', FRS') \<in> set (exec_instr (instrs_of (compP2 P) C M ! pc) (compP2 P) H stk loc C M pc FRS)`
  note pc = `pc < length (instrs_of (compP2 P) C M)`
  note check = `check_instr (instrs_of (compP2 P) C M ! pc) (compP2 P) H stk loc C M pc FRS`
  from bisim show ?thesis
  proof(cases)
    case (bl1_Normal C' M' Ts EXS FRS'' T body D ex STK LOC PC XCP)
    hence [simp]: "ex = (e, xs)" "EXS = exs" "STK = stk" "LOC = loc" "C' = C" "M' = M"
      "PC = pc" "FRS'' = FRS" "XCP = None" by simp_all
    note sees = `P \<turnstile> C' sees M': Ts\<rightarrow>T = body in D`
    from wf show ?thesis
    proof(rule \<tau>Red_simulates_exec_instr_aux1)
      from \<tau> show "\<tau>Move2 P (None, h, (stk, loc, C, M, pc) # FRS)" by(simp)
    next
      show "(TA, xcp', h', frs') \<in> set (exec_instr ((compE2 body @ [Return]) ! pc) (compP2 P) h stk loc C M pc FRS)"
	using exec pc sees by(auto simp add: compP2_def compMb2_def)
    next
      from pc sees show "pc < Suc (length (compE2 body))"
	by(simp add: compP2_def compMb2_def)
    next
      from check sees show "check_instr ((compE2 body @ [Return]) ! pc) (compP2 P) h stk loc C M pc FRS"
	by(simp add: compP2_def compMb2_def)
    next
      from `bisim1_list P h C' M' (length Ts) EXS FRS''`
      show "bisim1_list P h C M (length Ts) exs FRS" by simp
    next
      from sees show "P \<turnstile> C sees M: Ts\<rightarrow>T = body in D" by simp
    next
      from `P,blocks1 (Suc 0) Ts body,Suc 0,h \<turnstile> ex \<leftrightarrow> (STK, LOC, PC, XCP)`
      show "P,blocks1 (Suc 0) Ts body,Suc 0,h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, None)" by simp
    next
      from `exsconf P h T ex` show "exsconf P h T (e, xs)" by simp
    qed(rule `P \<turnstile> h \<surd>`)+
  next
    case bl1_finalVal with exec have False by auto
    thus ?thesis ..
  next
    case bl1_finalThrow with exec have False by auto
    thus ?thesis ..
  qed
next
  case (exec_1_Throw TA \<sigma> a H f FRS)
  hence [simp]: "H = h" "xcp = \<lfloor>a\<rfloor>" "frs = f # FRS" "TA = ta" "\<sigma> = (xcp', h', frs')"
    and xcp_step: "exception_step (compP2 P) (\<epsilon>, \<lfloor>a\<rfloor>, H, f # FRS) = (ta, xcp', h', frs')" by simp_all
  from bisim show ?thesis
  proof(cases)
    case (bl1_Normal C' M' Ts EXS FRS'' T body D ex STK LOC PC XCP)
    hence [simp]: "ex = (e, xs)" "EXS = exs" "XCP = xcp" "FRS'' = FRS" "f = (STK, LOC, C', M', PC)"
      and bl: "bisim1_list P h C' M' (length Ts) exs FRS"
      and sees: "P \<turnstile> C' sees M': Ts\<rightarrow>T = body in D"
      and b: "P,blocks1 (Suc 0) Ts body,Suc 0,h \<turnstile> (e, xs) \<leftrightarrow> (STK, LOC, PC, \<lfloor>a\<rfloor>)"
      and exs: "exsconf P h T (e, xs)"
      and hconf: "P \<turnstile> h \<surd>" by simp_all
    from b have PC: "PC < length (compE2 body)" by(auto dest: bisim1_xcpD)
    from sees_method_compP[OF sees, of compMb2] obtain msl mxs ins xt
      where sees2: "compP2 P \<turnstile> C' sees M':Ts\<rightarrow>T = (msl, mxs, compE2 body @ [Return], compxE2 body 0 0) in D"
      by(simp add: compP2_def compMb2_def)
    show ?thesis
    proof(cases "match_ex_table (compP2 P) (cname_of h a) PC (ex_table_of (compP2 P) C' M')")
      case None
      with \<tau> sees PC have False by auto
      thus ?thesis ..
    next
      case (Some pcd)
      then obtain pch d where match: "match_ex_table (compP2 P) (cname_of h a) PC (ex_table_of (compP2 P) C' M') = \<lfloor>(pch, d)\<rfloor>"
	by(cases pcd) auto
      with \<tau> sees PC have \<tau>': "\<tau>move2 body PC \<lfloor>a\<rfloor>" by(simp add: compP2_def compMb2_def)
      from match xcp_step have [simp]: "ta = \<epsilon>" "xcp' = None" "h' = h"
	"frs' = (Addr a # drop (length STK - d) STK, LOC, C', M', pch) # FRS" by simp_all
      from b match sees2
      have "d \<le> length STK" by(auto intro: bisim1_match_Some_stk_length simp add: compP2_def compMb2_def)
      with match sees2
      have execm: "exec_move P (blocks1 (Suc 0) Ts body) h (STK, LOC, PC, \<lfloor>a\<rfloor>) ta h' (Addr a # drop (length STK - d) STK, LOC, pch, None)"
	by(auto simp add: exec_move_def intro: exec_catch)
      from exs obtain C T' where wte: "P,[Class C],h \<turnstile>1 e : T'" and xs: "Suc (max_vars e) \<le> length xs"
	by(auto elim: exsconf.cases)
      from red1_simulates_exec_instr[OF wf hconf b[simplified] execm _ wte] xs PC obtain e'' xs''
	where b': "P,blocks1 (Suc 0) Ts body,Suc 0,h \<turnstile> (e'', xs'') \<leftrightarrow> (Addr a # drop (length STK - d) STK, LOC, pch, None)"
	and red: "\<tau>Red P h e xs e'' xs''" and [simp]: "h' = h" by(auto split: split_if_asm intro: \<tau>move2xcp)
      from red have Red: "\<tau>Red1 P h ((e, xs), exs) ((e'', xs''), exs)" by(rule \<tau>Red_into_\<tau>Red1)
      moreover from bl sees b' have "bisim1_list1 P h (e'', xs'') exs None ((Addr a # drop (length STK - d) STK, LOC, C', M', pch) # FRS)" using \<tau>Red1_preserves_sconf[OF wf hconf exs red] hconf by(rule bisim1_list1.bl1_Normal)
      ultimately show ?thesis by auto
    qed
  qed(simp_all)
qed

declare split_beta[simp]

lemma bisim1_Invoke_\<tau>Red:
  "\<lbrakk> P,E,n,h \<turnstile> (e, xs) \<leftrightarrow> (rev vs @ Addr a # stk', loc, pc, None); pc < length (compE2 E);
     compE2 E ! pc = Invoke M (length vs);  n + max_vars e \<le> length xs \<rbrakk>
  \<Longrightarrow> \<exists>e' xs'. \<tau>Red P h e xs e' xs' \<and> P,E,n,h \<turnstile> clearInitBlock e' xs' \<leftrightarrow> (rev vs @ Addr a # stk', loc, pc, None) \<and> call e' = \<lfloor>(a, M, vs)\<rfloor>"
  (is "\<lbrakk> _; _; _; _ \<rbrakk> \<Longrightarrow> ?concl e xs E n pc stk' loc")

  and bisims1_Invoke_\<tau>Reds:
  "\<lbrakk> P,Es,n,h \<turnstile> (es, xs) [\<leftrightarrow>] (rev vs @ Addr a # stk', loc, pc, None); pc < length (compEs2 Es);
    compEs2 Es ! pc = Invoke M (length vs); n + max_varss es \<le> length xs \<rbrakk>
  \<Longrightarrow> \<exists>es' xs'. \<tau>Reds P h es xs es' xs' \<and> P,Es,n,h \<turnstile> clearInitBlocks es' xs' [\<leftrightarrow>] (rev vs @ Addr a # stk', loc, pc, None) \<and> calls es' = \<lfloor>(a, M, vs)\<rfloor>"
  (is "\<lbrakk> _; _; _; _ \<rbrakk> \<Longrightarrow> ?concls es xs Es n pc stk' loc")
proof(induct E n e xs stk\<equiv>"rev vs @ Addr a # stk'" loc pc xcp\<equiv>"None::addr option"
  and Es n es xs stk\<equiv>"rev vs @ Addr a # stk'" loc pc xcp\<equiv>"None::addr option"
  arbitrary: stk' and stk' rule: bisim1_bisims1_inducts_split)
  case bisim1Val2 thus ?case by simp
next
  case bisim1New thus ?case by simp
next
  case bisim1NewThrow thus ?case by simp
next
  case bisim1NewArray thus ?case
    by(fastsimp split: split_if_asm intro: bisim1_bisims1.bisim1NewArray dest: bisim1_pc_length_compE2)
next
  case bisim1NewArrayNegative thus ?case by simp
next
  case bisim1NewArrayFail thus ?case by simp
next
  case bisim1NewArrayThrow thus ?case by simp
next
  case bisim1Cast thus ?case
    by(fastsimp split: split_if_asm intro: bisim1_bisims1.bisim1Cast dest: bisim1_pc_length_compE2)
next
  case bisim1CastThrow thus ?case by simp
next
  case bisim1CastFail thus ?case by simp
next
  case bisim1Val thus ?case by simp
next
  case bisim1Var thus ?case by simp
next
  case bisim1BinOp1 thus ?case
    by(fastsimp split: split_if_asm bop.splits intro: bisim1_bisims1.bisim1BinOp1 dest: bisim1_pc_length_compE2)
next
  case bisim1BinOpThrow1 thus ?case by simp
next
  case (bisim1BinOp2 e2 n e' xs stk loc pc xcp e1 bop v1)
  note IH = `\<And>stk'. \<lbrakk>pc < length (compE2 e2); compE2 e2 ! pc = Invoke M (length vs); n + max_vars e' \<le> length xs;
                     stk = rev vs @ Addr a # stk'; xcp = None \<rbrakk> \<Longrightarrow> ?concl e' xs e2 n pc stk' loc`
  note inv = `compE2 (e1 \<guillemotleft>bop\<guillemotright> e2) ! (length (compE2 e1) + pc) = Invoke M (length vs)`
  with `length (compE2 e1) + pc < length (compE2 (e1 \<guillemotleft>bop\<guillemotright> e2))` have pc: "pc < length (compE2 e2)"
    by(auto split: bop.splits split_if_asm)
  moreover with inv have "compE2 e2 ! pc = Invoke M (length vs)" by simp
  moreover with `P,e2,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)` `xcp = None` pc
  obtain vs'' v'' stk'' where "stk = vs'' @ v'' # stk''" and "length vs'' = length vs"
    by(auto dest!: bisim1_Invoke_stkD)
  with `stk @ [v1] = rev vs @ Addr a # stk'` obtain stk'''
    where stk''': "stk = rev vs @ Addr a # stk'''" and stk: "stk' = stk''' @ [v1]"
    by(cases stk' rule: rev_cases) auto
  from `n + max_vars (Val v1 \<guillemotleft>bop\<guillemotright> e') \<le> length xs` have "n + max_vars e' \<le> length xs" by simp
  ultimately have "?concl e' xs e2 n pc stk''' loc" using stk''' `xcp = None` by(rule IH)
  then obtain e'' xs' where IH': "\<tau>Red P h e' xs e'' xs'" "call e'' = \<lfloor>(a, M, vs)\<rfloor>"
    and bisim: "P,e2,n,h \<turnstile> clearInitBlock e'' xs' \<leftrightarrow> (rev vs @ Addr a # stk''', loc, pc, None)" by blast
  from bisim `bsok e1 n` have "P,e1\<guillemotleft>bop\<guillemotright>e2,n,h \<turnstile> (Val v1 \<guillemotleft>bop\<guillemotright> fst (clearInitBlock e'' xs'), snd (clearInitBlock e'' xs')) \<leftrightarrow> ((rev vs @ Addr a # stk''') @ [v1], loc, length (compE2 e1) + pc, None)"
    by -(rule bisim1_bisims1.bisim1BinOp2, auto)
  with IH' stk show ?case by(fastsimp)
next
  case bisim1BinOpThrow2 thus ?case by simp
next
  case bisim1LAss1 thus ?case
    by(fastsimp split: split_if_asm intro: bisim1_bisims1.bisim1LAss1 dest: bisim1_pc_length_compE2)
next
  case bisim1LAss2 thus ?case by simp
next
  case bisim1LAssThrow thus ?case by simp
next
  case bisim1AAcc1 thus ?case
    by(fastsimp split: split_if_asm intro: bisim1_bisims1.bisim1AAcc1 dest: bisim1_pc_length_compE2)
next
  case bisim1AAccThrow1 thus ?case by simp
next
  case (bisim1AAcc2 e2 n e' xs stk loc pc xcp e1 v1)
  note IH = `\<And>stk'. \<lbrakk>pc < length (compE2 e2); compE2 e2 ! pc = Invoke M (length vs); n + max_vars e' \<le> length xs;
                     stk = rev vs @ Addr a # stk'; xcp = None \<rbrakk> \<Longrightarrow> ?concl e' xs e2 n pc stk' loc`
  note inv = `compE2 (e1\<lfloor>e2\<rceil>) ! (length (compE2 e1) + pc) = Invoke M (length vs)`
  with `length (compE2 e1) + pc < length (compE2 (e1\<lfloor>e2\<rceil>))` have pc: "pc < length (compE2 e2)"
    by(auto split: split_if_asm)
  moreover with inv have "compE2 e2 ! pc = Invoke M (length vs)" by simp
  moreover with `P,e2,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)` `xcp = None` pc
  obtain vs'' v'' stk'' where "stk = vs'' @ v'' # stk''" and "length vs'' = length vs"
    by(auto dest!: bisim1_Invoke_stkD)
  with `stk @ [v1] = rev vs @ Addr a # stk'` obtain stk'''
    where stk''': "stk = rev vs @ Addr a # stk'''" and stk: "stk' = stk''' @ [v1]"
    by(cases stk' rule: rev_cases) auto
  from `n + max_vars (Val v1\<lfloor>e'\<rceil>) \<le> length xs` have "n + max_vars e' \<le> length xs" by simp
  ultimately have "?concl e' xs e2 n pc stk''' loc" using stk''' `xcp = None` by(rule IH)
  then obtain e'' xs' where IH': "\<tau>Red P h e' xs e'' xs'" "call e'' = \<lfloor>(a, M, vs)\<rfloor>"
    and bisim: "P,e2,n,h \<turnstile> clearInitBlock e'' xs' \<leftrightarrow> (rev vs @ Addr a # stk''', loc, pc, None)" by blast
  from bisim `bsok e1 n` have "P,e1\<lfloor>e2\<rceil>,n,h \<turnstile> (Val v1\<lfloor>fst (clearInitBlock e'' xs')\<rceil>, snd (clearInitBlock e'' xs')) \<leftrightarrow> ((rev vs @ Addr a # stk''') @ [v1], loc, length (compE2 e1) + pc, None)"
    by -(rule bisim1_bisims1.bisim1AAcc2, auto)
  with IH' stk show ?case by(fastsimp)
next
  case bisim1AAccThrow2 thus ?case by simp
next
  case bisim1AAccNull thus ?case by simp
next
  case bisim1AAccBounds thus ?case by simp
next
  case (bisim1AAss1 e n e' xs stk loc pc xcp e2 e3)
  note IH = `\<And>stk'. \<lbrakk>pc < length (compE2 e); compE2 e ! pc = Invoke M (length vs); n + max_vars e' \<le> length xs;
                     stk = rev vs @ Addr a # stk'; xcp = None\<rbrakk> \<Longrightarrow> ?concl e' xs e n pc stk' loc`
  note bisim = `P,e,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note len = `n + max_vars (e'\<lfloor>e2\<rceil> := e3) \<le> length xs`
  hence len': "n + max_vars e' \<le> length xs" by simp
  note stk = `stk = rev vs @ Addr a # stk'`
  note inv = `compE2 (e\<lfloor>e2\<rceil> := e3) ! pc = Invoke M (length vs)`
  with `pc < length (compE2 (e\<lfloor>e2\<rceil> := e3))` bisim have pc: "pc < length (compE2 e)"
    by(auto split: split_if_asm dest: bisim1_pc_length_compE2)
  moreover with inv have "compE2 e ! pc = Invoke M (length vs)" by simp
  ultimately have "?concl e' xs e n pc stk' loc" using len' stk `xcp = None` by(rule IH)
  thus ?case using `bsok e2 n` `bsok e3 n` by(fastsimp intro: bisim1_bisims1.bisim1AAss1)
next
  case bisim1AAssThrow1 thus ?case by simp
next
  case (bisim1AAss2 e2 n e' xs stk loc pc xcp e1 e3 v1)
  note IH = `\<And>stk'. \<lbrakk>pc < length (compE2 e2); compE2 e2 ! pc = Invoke M (length vs); n + max_vars e' \<le> length xs;
                     stk = rev vs @ Addr a # stk'; xcp = None \<rbrakk> \<Longrightarrow> ?concl e' xs e2 n pc stk' loc`
  note inv = `compE2 (e1\<lfloor>e2\<rceil> := e3) ! (length (compE2 e1) + pc) = Invoke M (length vs)`
  note bisim = `P,e2,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  with inv `length (compE2 e1) + pc < length (compE2 (e1\<lfloor>e2\<rceil> := e3))` have pc: "pc < length (compE2 e2)"
    by(auto split: split_if_asm dest: bisim1_pc_length_compE2)
  moreover with inv have "compE2 e2 ! pc = Invoke M (length vs)" by simp
  moreover with bisim `xcp = None` pc
  obtain vs'' v'' stk'' where "stk = vs'' @ v'' # stk''" and "length vs'' = length vs"
    by(auto dest!: bisim1_Invoke_stkD)
  with `stk @ [v1] = rev vs @ Addr a # stk'` obtain stk'''
    where stk''': "stk = rev vs @ Addr a # stk'''" and stk: "stk' = stk''' @ [v1]"
    by(cases stk' rule: rev_cases) auto
  from `n + max_vars (Val v1\<lfloor>e'\<rceil> := e3) \<le> length xs` have "n + max_vars e' \<le> length xs" by simp
  ultimately have "?concl e' xs e2 n pc stk''' loc" using stk''' `xcp = None` by(rule IH)
  then obtain e'' xs' where IH': "\<tau>Red P h e' xs e'' xs'" "call e'' = \<lfloor>(a, M, vs)\<rfloor>"
    and bisim: "P,e2,n,h \<turnstile> clearInitBlock e'' xs' \<leftrightarrow> (rev vs @ Addr a # stk''', loc, pc, None)" by blast
  from bisim `bsok e1 n` `bsok e3 n`
  have "P,e1\<lfloor>e2\<rceil> := e3,n,h \<turnstile> (Val v1\<lfloor>fst (clearInitBlock e'' xs')\<rceil> := e3, snd (clearInitBlock e'' xs')) \<leftrightarrow> ((rev vs @ Addr a # stk''') @ [v1], loc, length (compE2 e1) + pc, None)"
    by -(rule bisim1_bisims1.bisim1AAss2, auto)
  with IH' stk show ?case by(fastsimp)
next
  case (bisim1AAss3 e3 n e' xs stk loc pc xcp e1 e2 v1 v2)
  note IH = `\<And>stk'. \<lbrakk>pc < length (compE2 e3); compE2 e3 ! pc = Invoke M (length vs); n + max_vars e' \<le> length xs;
                     stk = rev vs @ Addr a # stk'; xcp = None \<rbrakk> \<Longrightarrow> ?concl e' xs e3 n pc stk' loc`
  note inv = `compE2 (e1\<lfloor>e2\<rceil> := e3) ! (length (compE2 e1) + length (compE2 e2) + pc) = Invoke M (length vs)`
  with `length (compE2 e1) + length (compE2 e2) + pc < length (compE2 (e1\<lfloor>e2\<rceil> := e3))`
  have pc: "pc < length (compE2 e3)" by(simp add: nth_Cons split: nat.split_asm split_if_asm)
  moreover with inv have "compE2 e3 ! pc = Invoke M (length vs)" by simp
  moreover with `P,e3,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)` `xcp = None` pc
  obtain vs'' v'' stk'' where "stk = vs'' @ v'' # stk''" and "length vs'' = length vs"
    by(auto dest!: bisim1_Invoke_stkD)
  with `stk @ [v2, v1] = rev vs @ Addr a # stk'` obtain stk'''
    where stk''': "stk = rev vs @ Addr a # stk'''" and stk: "stk' = stk''' @ [v2, v1]"
    by(cases stk' rule: rev_cases) auto
  from `n + max_vars (Val v1\<lfloor>Val v2\<rceil> := e') \<le> length xs` have "n + max_vars e' \<le> length xs" by simp
  ultimately have "?concl e' xs e3 n pc stk''' loc" using stk''' `xcp = None` by(rule IH)
  then obtain e'' xs' where IH': "\<tau>Red P h e' xs e'' xs'" "call e'' = \<lfloor>(a, M, vs)\<rfloor>"
    and bisim: "P,e3,n,h \<turnstile> clearInitBlock e'' xs' \<leftrightarrow> (rev vs @ Addr a # stk''', loc, pc, None)" by blast
  from bisim `bsok e1 n` `bsok e2 n`
  have "P,e1\<lfloor>e2\<rceil> := e3,n,h \<turnstile> (Val v1\<lfloor>Val v2\<rceil> := fst (clearInitBlock e'' xs'), snd (clearInitBlock e'' xs')) \<leftrightarrow> ((rev vs @ Addr a # stk''') @ [v2, v1], loc, length (compE2 e1) + length (compE2 e2) + pc, None)"
    by -(rule bisim1_bisims1.bisim1AAss3, auto)
  with IH' stk show ?case by(fastsimp)
next
  case bisim1AAssThrow2 thus ?case by simp
next
  case bisim1AAssThrow3 thus ?case by simp
next
  case bisim1AAssNull thus ?case by simp
next
  case bisim1AAssBounds thus ?case by simp
next
  case bisim1AAssStore thus ?case by simp
next
  case bisim1AAss4 thus ?case by simp
next
  case bisim1ALength thus ?case
    by(fastsimp split: split_if_asm intro: bisim1_bisims1.bisim1ALength dest: bisim1_pc_length_compE2)
next
  case bisim1ALengthNull thus ?case by simp
next
  case bisim1ALengthThrow thus ?case by simp
next
  case bisim1FAcc thus ?case
    by(fastsimp split: split_if_asm intro: bisim1_bisims1.bisim1FAcc dest: bisim1_pc_length_compE2)
next
  case bisim1FAccNull thus ?case by simp
next
  case bisim1FAccThrow thus ?case by simp
next
  case bisim1FAss1 thus ?case
    by(fastsimp split: split_if_asm intro: bisim1_bisims1.bisim1FAss1 dest: bisim1_pc_length_compE2)
next
  case bisim1FAssThrow1 thus ?case by simp
next
  case (bisim1FAss2 e2 n e' xs stk loc pc xcp e1 F D v1)
  note IH = `\<And>stk'. \<lbrakk>pc < length (compE2 e2); compE2 e2 ! pc = Invoke M (length vs); n + max_vars e' \<le> length xs;
                     stk = rev vs @ Addr a # stk'; xcp = None \<rbrakk> \<Longrightarrow> ?concl e' xs e2 n pc stk' loc`
  note inv = `compE2 (e1\<bullet>F{D} := e2) ! (length (compE2 e1) + pc) = Invoke M (length vs)`
  with `length (compE2 e1) + pc < length (compE2 (e1\<bullet>F{D} := e2))` have pc: "pc < length (compE2 e2)"
    by(simp split: split_if_asm nat.split_asm add: nth_Cons)
  moreover with inv have "compE2 e2 ! pc = Invoke M (length vs)" by simp
  moreover with `P,e2,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)` `xcp = None` pc
  obtain vs'' v'' stk'' where "stk = vs'' @ v'' # stk''" and "length vs'' = length vs"
    by(auto dest!: bisim1_Invoke_stkD)
  with `stk @ [v1] = rev vs @ Addr a # stk'` obtain stk'''
    where stk''': "stk = rev vs @ Addr a # stk'''" and stk: "stk' = stk''' @ [v1]"
    by(cases stk' rule: rev_cases) auto
  from `n + max_vars (Val v1\<bullet>F{D} := e') \<le> length xs` have "n + max_vars e' \<le> length xs" by simp
  ultimately have "?concl e' xs e2 n pc stk''' loc" using stk''' `xcp = None` by(rule IH)
  then obtain e'' xs' where IH': "\<tau>Red P h e' xs e'' xs'" "call e'' = \<lfloor>(a, M, vs)\<rfloor>"
    and bisim: "P,e2,n,h \<turnstile> clearInitBlock e'' xs' \<leftrightarrow> (rev vs @ Addr a # stk''', loc, pc, None)" by blast
  from bisim `bsok e1 n` have "P,e1\<bullet>F{D} := e2,n,h \<turnstile> (Val v1\<bullet>F{D} := fst (clearInitBlock e'' xs'), snd (clearInitBlock e'' xs')) \<leftrightarrow> ((rev vs @ Addr a # stk''') @ [v1], loc, length (compE2 e1) + pc, None)"
    by -(rule bisim1_bisims1.bisim1FAss2, auto)
  with IH' stk show ?case by(fastsimp)
next
  case bisim1FAssThrow2 thus ?case by simp
next
  case bisim1FAssNull thus ?case by simp
next
  case bisim1FAss3 thus ?case by simp
next
  case (bisim1Call1 obj n obj' xs stk loc pc xcp ps M')
  note IH = `\<And>stk'. \<lbrakk>pc < length (compE2 obj); compE2 obj ! pc = Invoke M (length vs); n + max_vars obj' \<le> length xs; 
                     stk = rev vs @ Addr a # stk'; xcp = None\<rbrakk> \<Longrightarrow> ?concl obj' xs obj n pc stk' loc`
  note bisim = `P,obj,n,h \<turnstile> (obj', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note len = `n + max_vars (obj'\<bullet>M'(ps)) \<le> length xs`
  hence len': "n + max_vars obj' \<le> length xs" by simp
  note stk = `stk = rev vs @ Addr a # stk'`
  note inv = `compE2 (obj\<bullet>M'(ps)) ! pc = Invoke M (length vs)`
  with `pc < length (compE2 (obj\<bullet>M'(ps)))` bisim have pc: "pc < length (compE2 obj) \<or> ps = [] \<and> pc = length (compE2 obj)"
    by(cases ps)(auto split: bop.splits split_if_asm dest: bisim1_pc_length_compE2)
  thus ?case
  proof
    assume "pc < length (compE2 obj)"
    moreover with inv have "compE2 obj ! pc = Invoke M (length vs)" by simp
    ultimately have "?concl obj' xs obj n pc stk' loc" using len' stk `xcp = None` by(rule IH)
    thus ?thesis using `bsoks ps n` by(fastsimp intro: bisim1_bisims1.bisim1Call1)
  next
    assume [simp]: "ps = [] \<and> pc = length (compE2 obj)"
    with inv have [simp]: "vs = []" "M' = M" by simp_all
    with stk bisim have [simp]: "stk = [Addr a]" by(auto dest: bisim1_pc_length_compE2D)
    with bisim len' `xcp = None` have "\<tau>Red P h obj' xs (addr a) loc" by(auto intro: bisim1_Val_\<tau>Red)
    moreover from `bsok obj n`
    have "P,obj\<bullet>M([]),n,h \<turnstile> (addr a\<bullet>M([]), loc) \<leftrightarrow> ([Addr a], loc, length (compE2 obj), None)"
      by(rule bisim1_bisims1.bisim1Call1[OF bisim1Val2]) simp
    ultimately show ?thesis using stk by auto fastsimp
  qed
next
  case (bisim1CallParams ps n ps' xs stk loc pc xcp obj M' v)
  note IH = `\<And>stk'. \<lbrakk>pc < length (compEs2 ps); compEs2 ps ! pc = Invoke M (length vs); n + max_varss ps' \<le> length xs;
                     stk = rev vs @ Addr a # stk'; xcp = None\<rbrakk> \<Longrightarrow> ?concls ps' xs ps n pc stk' loc`
  note bisim = `P,ps,n,h \<turnstile> (ps', xs) [\<leftrightarrow>] (stk, loc, pc, xcp)`
  note len = `n + max_vars (Val v\<bullet>M'(ps')) \<le> length xs`
  hence len': "n + max_varss ps' \<le> length xs" by simp
  note stk = `stk @ [v] = rev vs @ Addr a # stk'`
  note inv = `compE2 (obj\<bullet>M'(ps)) ! (length (compE2 obj) + pc) = Invoke M (length vs)`
  from `length (compE2 obj) + pc < length (compE2 (obj\<bullet>M'(ps)))` 
  have "pc < length (compEs2 ps) \<or> pc = length (compEs2 ps)" by(auto)
  thus ?case
  proof
    assume pc: "pc < length (compEs2 ps)"
    moreover with inv have "compEs2 ps ! pc = Invoke M (length vs)" by simp
    moreover with bisim `xcp = None` pc
    obtain vs'' v'' stk'' where "stk = vs'' @ v'' # stk''" and "length vs'' = length vs"
      by(auto dest!: bisims1_Invoke_stkD)
    with `stk @ [v] = rev vs @ Addr a # stk'` obtain stk'''
      where stk''': "stk = rev vs @ Addr a # stk'''" and stk: "stk' = stk''' @ [v]"
      by(cases stk' rule: rev_cases) auto
    note len' stk''' `xcp = None`
    ultimately have "?concls ps' xs ps n pc stk''' loc" by(rule IH)
    then obtain es'' xs' where IH': "\<tau>Reds P h ps' xs es'' xs'" "calls es'' = \<lfloor>(a, M, vs)\<rfloor>"
      and bisim: "P,ps,n,h \<turnstile> clearInitBlocks es'' xs' [\<leftrightarrow>] (rev vs @ Addr a # stk''', loc, pc, None)" by blast
    from bisim `bsok obj n` have "P,obj\<bullet>M'(ps),n,h \<turnstile> (Val v\<bullet>M'(fst (clearInitBlocks es'' xs')), snd (clearInitBlocks es'' xs')) \<leftrightarrow> ((rev vs @ Addr a # stk''') @ [v], loc, length (compE2 obj) + pc, None)" by-(rule bisim1_bisims1.bisim1CallParams, auto)
    with IH' stk show ?case by fastsimp
  next
    assume [simp]: "pc = length (compEs2 ps)"
    from bisim obtain vs' where [simp]: "stk = rev vs'"
      and psvs': "length ps = length vs'" by(auto dest: bisims1_pc_length_compEs2D)
    from inv have [simp]: "M' = M" and vsps: "length vs = length ps" by simp_all
    with stk psvs' have [simp]: "v = Addr a" "stk' = []" "vs' = vs" by simp_all
    from bisim len' `xcp = None` have "\<tau>Reds P h ps' xs (map Val vs) loc" by(auto intro: bisims1_Val_\<tau>Reds)
    moreover from bisims1_map_Val_append[OF bisims1Nil `bsoks ps n` vsps[symmetric], simplified, of P h loc] `bsok obj n`
    have "P,obj\<bullet>M(ps),n,h \<turnstile> (addr a\<bullet>M(map Val vs), loc) \<leftrightarrow> (rev vs @ [Addr a], loc, length (compE2 obj) + length (compEs2 ps), None)"
      by(rule bisim1_bisims1.bisim1CallParams)
    ultimately show ?thesis by fastsimp
  qed
next
  case bisim1CallThrow thus ?case by simp
next
  case bisim1CallThrowObj thus ?case by simp
next
  case bisim1CallThrowParams thus ?case by simp
next
  case bisim1BlockSome1 thus ?case by simp
next
  case bisim1BlockSome2 thus ?case by simp
next
  case (bisim1BlockSome3 e V e' xs v stk loc pc xcp T)
  note IH = `\<And>stk'. \<lbrakk>pc < length (compE2 e); compE2 e ! pc = Invoke M (length vs);
                     Suc V + max_vars e' \<le> length (xs[V := v]); stk = rev vs @ Addr a # stk'; xcp = None \<rbrakk>
            \<Longrightarrow> ?concl e' (xs[V := v]) e (Suc V) pc stk' loc`
  from `Suc (Suc pc) < length (compE2 {V:T=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub>)` have "pc < length (compE2 e)" by simp
  moreover from `compE2 {V:T=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub> ! Suc (Suc pc) = Invoke M (length vs)`
  have "compE2 e ! pc = Invoke M (length vs)" by simp
  moreover note len = `V + max_vars {V:T=\<lfloor>v\<rfloor>; e'}\<^bsub>False\<^esub> \<le> length xs`
  hence "Suc V + max_vars e' \<le> length (xs[V := v])" by simp
  ultimately have "?concl e' (xs[V := v]) e (Suc V) pc stk' loc" using `stk = rev vs @ Addr a # stk'` `xcp = None` by(rule IH)
  then obtain e'' xs' where red: "\<tau>Red P h e' (xs[V := v]) e'' xs'"
    and bisim': "P,e,Suc V,h \<turnstile> clearInitBlock e'' xs' \<leftrightarrow> (rev vs @ Addr a # stk', loc, pc, None)"
    and call: "call e'' = \<lfloor>(a, M, vs)\<rfloor>" by blast
  from red show ?case
  proof(cases rule: converse_\<tau>RedE[case_names refl step])
    case refl thus ?thesis using bisim' call by(fastsimp intro: \<tau>Red_refl bisim1_bisims1.bisim1BlockSome4)
  next
    case (step e''' xs''')
    note red = `P \<turnstile>1 \<langle>e',(h, xs[V := v])\<rangle> -\<epsilon>\<rightarrow> \<langle>e''',(h, xs''')\<rangle>`
    note Red = `\<tau>Red P h e''' xs''' e'' xs'`
    from len have V: "V < length xs" by simp
    with red have "P \<turnstile>1 \<langle>{V:T=\<lfloor>v\<rfloor>; e'}\<^bsub>False\<^esub>, (h, xs)\<rangle> -\<epsilon>\<rightarrow> \<langle>{V:T=None; e'''}\<^bsub>False\<^esub>, (h, xs''')\<rangle>" by(auto intro: Block1RedSome)
    moreover from `\<tau>move1 e'` have "\<tau>move1 {V:T=\<lfloor>v\<rfloor>; e'}\<^bsub>False\<^esub>" by(rule \<tau>move1Block)
    moreover from V red Red have "V < length xs'" by(auto dest!: red1_preserves_len \<tau>Red_preserves_len)
    with Red have "\<tau>Red P h {V:T=None; e'''}\<^bsub>False\<^esub> xs''' {V:T=None; e''}\<^bsub>False\<^esub> xs'" by(rule Block_\<tau>Red_None)
    ultimately have "\<tau>Red P h {V:T=\<lfloor>v\<rfloor>; e'}\<^bsub>False\<^esub> xs {V:T=None; e''}\<^bsub>False\<^esub> xs'" by(rule converse_\<tau>Red_step)
    with bisim' call show ?thesis by(fastsimp intro: bisim1_bisims1.bisim1BlockSome4)
  qed
next
  case (bisim1BlockSome4 e V e' xs stk loc pc xcp T v)
  note IH = `\<And>stk'. \<lbrakk>pc < length (compE2 e); compE2 e ! pc = Invoke M (length vs); Suc V + max_vars e' \<le> length xs;
                     stk = rev vs @ Addr a # stk'; xcp = None \<rbrakk> \<Longrightarrow> ?concl e' xs e (Suc V) pc stk' loc`
  from `Suc (Suc pc) < length (compE2 {V:T=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub>)` have "pc < length (compE2 e)" by simp
  moreover from `compE2 {V:T=\<lfloor>v\<rfloor>; e}\<^bsub>False\<^esub> ! Suc (Suc pc) = Invoke M (length vs)`
  have "compE2 e ! pc = Invoke M (length vs)" by simp
  moreover note len = `V + max_vars {V:T=None; e'}\<^bsub>False\<^esub> \<le> length xs`
  hence "Suc V + max_vars e' \<le> length xs" by simp
  ultimately have "?concl e' xs e (Suc V) pc stk' loc" using `stk = rev vs @ Addr a # stk'` `xcp = None` by(rule IH)
  then obtain e'' xs' where red: "\<tau>Red P h e' xs e'' xs'"
    and bisim': "P,e,Suc V,h \<turnstile> clearInitBlock e'' xs' \<leftrightarrow> (rev vs @ Addr a # stk', loc, pc, None)"
    and call: "call e'' = \<lfloor>(a, M, vs)\<rfloor>" by blast
  from red have "length xs' = length xs" by(auto dest: \<tau>Red_preserves_len)
  with red len have "\<tau>Red P h {V:T=None; e'}\<^bsub>False\<^esub> xs {V:T=None; e''}\<^bsub>False\<^esub> xs'" by(auto)
  with bisim' call show ?case by(fastsimp intro: bisim1_bisims1.bisim1BlockSome4)
next
  case bisim1BlockThrowSome thus ?case by simp
next
  case (bisim1BlockNone e V e' xs stk loc pc xcp T)
  note IH = `\<And>stk'. \<lbrakk>pc < length (compE2 e); compE2 e ! pc = Invoke M (length vs); Suc V + max_vars e' \<le> length xs;
                     stk = rev vs @ Addr a # stk'; xcp = None \<rbrakk> \<Longrightarrow> ?concl e' xs e (Suc V) pc stk' loc`
  from `pc < length (compE2 {V:T=None; e}\<^bsub>False\<^esub>)` have "pc < length (compE2 e)" by simp
  moreover from `compE2 {V:T=None; e}\<^bsub>False\<^esub> ! pc = Invoke M (length vs)`
  have "compE2 e ! pc = Invoke M (length vs)" by simp
  moreover note len = `V + max_vars {V:T=None; e'}\<^bsub>False\<^esub> \<le> length xs`
  hence "Suc V + max_vars e' \<le> length xs" by simp
  ultimately have "?concl e' xs e (Suc V) pc stk' loc" using `stk = rev vs @ Addr a # stk'` `xcp = None` by(rule IH)
  then obtain e'' xs' where red: "\<tau>Red P h e' xs e'' xs'"
    and bisim': "P,e,Suc V,h \<turnstile> clearInitBlock e'' xs' \<leftrightarrow> (rev vs @ Addr a # stk', loc, pc, None)"
    and call: "call e'' = \<lfloor>(a, M, vs)\<rfloor>" by blast
  from red have "length xs' = length xs" by(auto dest: \<tau>Red_preserves_len)
  with red len have "\<tau>Red P h {V:T=None; e'}\<^bsub>False\<^esub> xs {V:T=None; e''}\<^bsub>False\<^esub> xs'" by(auto)
  with bisim' call show ?case by(fastsimp intro: bisim1_bisims1.bisim1BlockNone)
next
  case bisim1BlockThrowNone thus ?case by simp
next
  case bisim1Sync1 thus ?case
    by(fastsimp split: split_if_asm intro: bisim1_bisims1.bisim1Sync1 dest: bisim1_pc_length_compE2)
next
  case bisim1Sync2 thus ?case by simp
next
  case bisim1Sync3 thus ?case by simp
next
  case bisim1Sync4 thus ?case
    by(fastsimp split: split_if_asm intro: bisim1_bisims1.bisim1Sync4 dest: bisim1_pc_length_compE2)
next
  case bisim1Sync5 thus ?case by simp
next
  case bisim1Sync6 thus ?case by simp
next
  case bisim1Sync7 thus ?case by simp
next
  case bisim1Sync8 thus ?case by simp
next
  case bisim1Sync9 thus ?case by simp
next
  case bisim1Sync10 thus ?case by simp
next
  case bisim1Sync11 thus ?case by simp
next
  case bisim1Sync12 thus ?case by simp
next
  case bisim1Sync13 thus ?case by simp
next
  case bisim1Sync14 thus ?case by simp
next
  case bisim1Sync15 thus ?case by simp
next
  case bisim1SyncThrow thus ?case by simp
next
  case bisim1Seq1 thus ?case
    by(fastsimp split: split_if_asm intro: bisim1_bisims1.bisim1Seq1 dest: bisim1_pc_length_compE2)
next
  case bisim1SeqThrow1 thus ?case by simp
next
  case bisim1Seq2 thus ?case
    by(fastsimp split: split_if_asm intro: bisim1_bisims1.bisim1Seq2 dest: bisim1_pc_length_compE2)
next
  case bisim1Cond1 thus ?case
    apply(clarsimp split: split_if_asm)
     apply(erule meta_allE, erule meta_impE, rule refl, clarify)
     apply(fastsimp intro!: exI intro: bisim1_bisims1.bisim1Cond1)
    by(fastsimp dest: bisim1_pc_length_compE2)
next
  case bisim1CondThen thus ?case
    apply(clarsimp split: split_if_asm)
     apply(erule meta_allE, erule meta_impE, rule refl, clarify)
     apply(fastsimp intro!: exI intro: bisim1_bisims1.bisim1CondThen)
    by(fastsimp dest: bisim1_pc_length_compE2)
next
  case bisim1CondElse thus ?case
    apply(clarsimp split: split_if_asm)
    apply(erule meta_allE, erule meta_impE, rule refl, clarify)
    by(fastsimp intro!: exI intro: bisim1_bisims1.bisim1CondElse)
next
  case bisim1CondThrow thus ?case by simp
next
  case bisim1While1 thus ?case by simp
next
  case bisim1While3 thus ?case
    by(fastsimp split: split_if_asm intro: bisim1_bisims1.bisim1While3 dest: bisim1_pc_length_compE2)
next
  case bisim1While4 thus ?case
    by(fastsimp split: split_if_asm intro: bisim1_bisims1.bisim1While4 dest: bisim1_pc_length_compE2)
next
  case bisim1While6 thus ?case by simp
next
  case bisim1While7 thus ?case by simp
next
  case bisim1WhileThrow1 thus ?case by simp
next
  case bisim1WhileThrow2 thus ?case by simp
next
  case bisim1Throw1 thus ?case
    by(fastsimp split: split_if_asm intro: bisim1_bisims1.bisim1Throw1 dest: bisim1_pc_length_compE2)
next
  case bisim1Throw2 thus ?case by simp
next
  case bisim1ThrowNull thus ?case by simp
next
  case bisim1ThrowThrow thus ?case by simp
next
  case bisim1Try thus ?case
    by(fastsimp split: split_if_asm intro: bisim1_bisims1.bisim1Try dest: bisim1_pc_length_compE2)
next
  case bisim1TryCatch1 thus ?case by simp
next
  case (bisim1TryCatch2 e V e' xs stk loc pc xcp e1 C)
  note IH = `\<And>stk'. \<lbrakk>pc < length (compE2 e); compE2 e ! pc = Invoke M (length vs); Suc V + max_vars e' \<le> length xs;
                     stk = rev vs @ Addr a # stk'; xcp = None \<rbrakk> \<Longrightarrow> ?concl e' xs e (Suc V) pc stk' loc`
  from `Suc (Suc (length (compE2 e1) + pc)) < length (compE2 (try e1 catch(C V) e))`
  have "pc < length (compE2 e)" by simp
  moreover from `compE2 (try e1 catch(C V) e) ! Suc (Suc (length (compE2 e1) + pc)) = Invoke M (length vs)`
  have "compE2 e ! pc = Invoke M (length vs)" by simp
  moreover note len = `V + max_vars {V:Class C=None; e'}\<^bsub>False\<^esub> \<le> length xs`
  hence "Suc V + max_vars e' \<le> length xs" by simp
  ultimately have "?concl e' xs e (Suc V) pc stk' loc" using `stk = rev vs @ Addr a # stk'` `xcp = None` by(rule IH)
  then obtain e'' xs' where red: "\<tau>Red P h e' xs e'' xs'"
    and bisim': "P,e,Suc V,h \<turnstile> clearInitBlock e'' xs' \<leftrightarrow> (rev vs @ Addr a # stk', loc, pc, None)"
    and call: "call e'' = \<lfloor>(a, M, vs)\<rfloor>" by blast
  from red have "length xs' = length xs" by(auto dest: \<tau>Red_preserves_len)
  with red len have "\<tau>Red P h {V:Class C=None; e'}\<^bsub>False\<^esub> xs {V:Class C=None; e''}\<^bsub>False\<^esub> xs'" by(auto)
  with bisim' call `bsok e1 V` show ?case by(fastsimp intro: bisim1_bisims1.bisim1TryCatch2)
next
  case bisim1TryFail thus ?case by simp
next
  case bisim1TryCatchThrow thus ?case by simp
next
  case bisims1Nil thus ?case by simp
next
  case (bisims1List1 e n e' xs stk loc pc xcp es)
  note IH = `\<And>stk'. \<lbrakk>pc < length (compE2 e); compE2 e ! pc = Invoke M (length vs); n + max_vars e' \<le> length xs;
                     stk = rev vs @ Addr a # stk'; xcp = None\<rbrakk> \<Longrightarrow> ?concl e' xs e n pc stk' loc`
  note bisim = `P,e,n,h \<turnstile> (e', xs) \<leftrightarrow> (stk, loc, pc, xcp)`
  note len = `n + max_varss (e' # es) \<le> length xs`
  hence len': "n + max_vars e' \<le> length xs" by simp
  note stk = `stk = rev vs @ Addr a # stk'`
  note inv = `compEs2 (e # es) ! pc = Invoke M (length vs)`
  with `pc < length (compEs2 (e # es))` bisim have pc: "pc < length (compE2 e)"
    by(cases es)(auto split: split_if_asm dest: bisim1_pc_length_compE2)
  moreover with inv have "compE2 e ! pc = Invoke M (length vs)" by simp
  ultimately have "?concl e' xs e n pc stk' loc" using len' stk `xcp = None` by(rule IH)
  thus ?case using `bsoks es n` by(fastsimp intro: bisim1_bisims1.bisims1List1 \<tau>Red_inj_\<tau>Reds)
next
  case (bisims1List2 es n es' xs stk loc pc xcp e v)
  note IH = `\<And>stk'. \<lbrakk>pc < length (compEs2 es); compEs2 es ! pc = Invoke M (length vs); n + max_varss es' \<le> length xs;
                     stk = rev vs @ Addr a # stk'; xcp = None\<rbrakk> \<Longrightarrow> ?concls es' xs es n pc stk' loc`
  note bisim = `P,es,n,h \<turnstile> (es', xs) [\<leftrightarrow>] (stk, loc, pc, xcp)`
  note len = `n + max_varss (Val v # es') \<le> length xs`
  hence len': "n + max_varss es' \<le> length xs" by simp
  note stk = `stk @ [v] = rev vs @ Addr a # stk'`
  note inv = `compEs2 (e # es) ! (length (compE2 e) + pc) = Invoke M (length vs)`
  from `length (compE2 e) + pc < length (compEs2 (e # es))` have pc: "pc < length (compEs2 es)" by auto
  moreover with inv have "compEs2 es ! pc = Invoke M (length vs)" by simp
  moreover with bisim `xcp = None` pc
  obtain vs'' v'' stk'' where "stk = vs'' @ v'' # stk''" and "length vs'' = length vs"
    by(auto dest!: bisims1_Invoke_stkD)
  with `stk @ [v] = rev vs @ Addr a # stk'` obtain stk'''
    where stk''': "stk = rev vs @ Addr a # stk'''" and stk: "stk' = stk''' @ [v]"
    by(cases stk' rule: rev_cases) auto
  note len' stk''' `xcp = None`
  ultimately have "?concls es' xs es n pc stk''' loc" by(rule IH)
  then obtain es'' xs' where red: "\<tau>Reds P h es' xs es'' xs'" and call: "calls es'' = \<lfloor>(a, M, vs)\<rfloor>"
    and bisim: "P,es,n,h \<turnstile> clearInitBlocks es'' xs' [\<leftrightarrow>] (rev vs @ Addr a # stk''', loc, pc, None)" by blast
  from bisim `bsok e n` have "P,e#es,n,h \<turnstile> (Val v # fst (clearInitBlocks es'' xs'), snd (clearInitBlocks es'' xs')) [\<leftrightarrow>]
                                          ((rev vs @ Addr a # stk''') @ [v], loc, length (compE2 e) + pc, None)" 
    by-(rule bisim1_bisims1.bisims1List2, auto)
  moreover from red have "\<tau>Reds P h (Val v # es') xs (Val v # es'') xs'" by(rule \<tau>Reds_cons_\<tau>Reds)
  ultimately show ?case using stk call by fastsimp
qed

declare split_beta [simp del]

lemma \<tau>Red_simulates_exec_instr_aux2:
  assumes wf: "wf_J1_prog P"
  and \<tau>: "\<not> \<tau>Move2 P (None, h, (stk, loc, C, M, pc) # FRS)"
  and exec: "(ta, xcp', h', frs') \<in> set (exec_instr ((compE2 body @ [Return]) ! pc) (compP2 P) h stk loc C M pc FRS)"
  and pc: "pc < Suc (length (compE2 body))"
  and chk: "check_instr ((compE2 body @ [Return]) ! pc) (compP2 P) h stk loc C M pc FRS"
  and bl: "bisim1_list P h C M (length Ts) exs FRS"
  and sees: "P \<turnstile> C sees M: Ts\<rightarrow>T = body in D"
  and bisim: "P,blocks1 (Suc 0) Ts body,Suc 0,h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, None)"
  and exsconf: "exsconf P h T (e, xs)"
  and hconf: "P \<turnstile> h \<surd>"
  shows "\<exists>e' xs' exs' ta' e'' xs'' exs''. \<tau>Red1 P h ((e, xs), exs) ((e', xs'), exs') \<and>
                                      P \<turnstile>1 \<langle>(e', xs')/exs', h\<rangle> -ta'\<rightarrow> \<langle>(e'', xs'')/exs'', h'\<rangle> \<and>
                                      \<not> \<tau>Move1 ((e', xs'), exs') \<and> ta_bisim (wbisim1 P) ta' ta \<and>
                                      bisim1_list1 P h' (e'', xs'') exs'' xcp' frs'"
proof -
  from exsconf have len': "Suc 0 + max_vars e \<le> length xs" by(auto elim: exsconf.cases)
  show ?thesis
  proof(cases "length frs' = Suc (length FRS)")
    case True
    with exec have "\<exists>stk' loc' pc'. frs' = (stk', loc', C, M, pc') # FRS"
      by(cases "(compE2 body @ [Return]) ! pc")(auto split: split_if_asm sum.splits simp add: split_beta)
    then obtain stk' loc' pc' where [simp]: "frs' = (stk', loc', C, M, pc') # FRS" by blast
    from exec sees True pc chk
    have exec': "exec_move P (blocks1 (Suc 0) Ts body) h (stk, loc, pc, None) ta h' (stk', loc', pc', xcp')"
      apply(simp add: compP2_def compMb2_def exec_move_def split: split_if_asm)
      apply(rule exec_instr)
        apply(cases "compE2 body ! pc", auto simp add: split_beta neq_Nil_conv split: split_if_asm)
	apply(force split: sum.split_asm)
       apply(force split: sum.split_asm)
      apply(cases "compE2 body ! pc", auto simp add: split_beta neq_Nil_conv split: split_if_asm)
      done
    from exec' have "pc < length (compE2 body)" by(auto simp add: exec_move_def)
    with \<tau> sees have "\<not> \<tau>move2 body pc None" by(auto simp add: compP2_def compMb2_def)
    with red1_simulates_exec_instr[OF wf hconf bisim, simplified, OF exec'] len' exsconf
    obtain e' xs' ta' e'' xs'' where bisim': "P,blocks1 (Suc 0) Ts body,Suc 0,h' \<turnstile> (e'', xs'') \<leftrightarrow> (stk', loc', pc', xcp')"
      and red1: "\<tau>Red P h e xs e' xs'" 
      and red2: "P \<turnstile>1 \<langle>e',(h, xs')\<rangle> -ta'\<rightarrow> \<langle>e'',(h', xs'')\<rangle>"
      and ta': "ta_bisim (wbisim1 P) ta' ta"
      and \<tau>': "\<not> \<tau>move1 e'" by(fastsimp elim!: exsconf.cases)
    from red1 have Red1: "\<tau>Red1 P h ((e, xs), exs) ((e', xs'), exs)" by(rule \<tau>Red_into_\<tau>Red1)
    moreover from red2 have "P \<turnstile>1 \<langle>(e', xs')/exs, h\<rangle> -ta'\<rightarrow> \<langle>(e'', xs'')/exs, h'\<rangle>" by(rule red1Red)
    moreover from \<tau>' red2 have "\<not> \<tau>Move1 ((e', xs'), exs)" by auto
    moreover from red2 have "hext h h'" by(auto dest: red1_hext_incr)
    with bl have "bisim1_list P h' C M (length Ts) exs FRS" by(rule bisim1_list_hext_mono)
    hence "bisim1_list1 P h' (e'', xs'') exs xcp' ((stk', loc', C, M, pc') # FRS)" using sees bisim'
    proof(rule bisim1_list1.bl1_Normal)
      from red1 red2 have "length xs'' = length xs" by(auto dest!: \<tau>Red_preserves_len red1_preserves_len)
    next
      from exsconf red1 have exsconf': "exsconf P h T (e', xs')" by(rule \<tau>Red1_preserves_sconf[OF wf hconf])
      thus "exsconf P h' T (e'', xs'')" using red2 by(rule red1_preserves_exsconf[OF wf hconf])
      from exsconf' hconf red2 show "P \<turnstile> h' \<surd>" by(auto dest: red1_preserves_hconf elim!: exsconf.cases)
    qed
    moreover note ta'
    ultimately show ?thesis by fastsimp
  next
    case False
    with exec sees pc compE2_not_Return[of body]
    have "(pc = length (compE2 body) \<or> (\<exists>M n. compE2 body ! pc = Invoke M n)) \<and> xcp' = None"
      apply(cases "compE2 body ! pc")
      apply(auto split: split_if_asm sum.split_asm simp add: split_beta compP2_def compMb2_def)
      apply(metis in_set_conv_nth)+
      done
    hence [simp]: "xcp' = None"
      and "pc = length (compE2 body) \<or> (\<exists>M n. compE2 body ! pc = Invoke M n)" by simp_all
    moreover {
      assume [simp]: "pc = length (compE2 body)"
      from bisim have Bisim: "P,blocks1 (Suc 0) Ts body,Suc 0,h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, length (compE2 (blocks1 (Suc 0) Ts body)), None)" by simp
      then obtain v where [simp]: "stk = [v]" by(blast dest: bisim1_pc_length_compE2D)
      with Bisim len' have red: "\<tau>Red P h e xs (Val v) loc" by clarify (rule bisim1_Val_\<tau>Red)
      hence Red: "\<tau>Red1 P h ((e, xs), exs) ((Val v, loc), exs)" by(rule \<tau>Red_into_\<tau>Red1)
      
      have ?thesis
      proof(cases "FRS = []")
	case False
	then obtain f frs'' where [simp]: "FRS = f # frs''" by(fastsimp simp add: neq_Nil_conv)
	obtain stk'' loc'' C'' M'' pc'' where [simp]: "f = (stk'', loc'', C'', M'', pc'')" by(cases f)
	from bl obtain Ts' exs''' T'' body' D' E XS vs' a stk''' C''' fs Ts''' T''' meth
	  where Tsvs': "length Ts = length vs'"
	  and [simp]: "exs = (E, XS) # exs'''"
	  and stk'': "stk'' = rev vs' @ Addr a # stk'''"
	  and bl': "bisim1_list P h C'' M'' (length Ts') exs''' frs''"
	  and sees': "P \<turnstile> C'' sees M'': Ts'\<rightarrow>T'' = body' in D'"
	  and bisim': "P,blocks1 (Suc 0) Ts' body',Suc 0,h \<turnstile> (E, XS) \<leftrightarrow> (rev vs' @ Addr a # stk''', loc'', pc'', None)"
	  and call: "call E = \<lfloor>(a, M, vs')\<rfloor>"
	  and ha: "h a = \<lfloor>Obj C''' fs\<rfloor>"
	  and sees'': "P \<turnstile> C''' sees M: Ts'''\<rightarrow>T''' = meth in C"
	  and pc'': "compE2 body' ! pc'' = Invoke M (length vs')"
	  and exsconf'': "exsconf P h T'' (E, XS)"
	  by -(erule bisim1_list.cases, auto, blast)
	from call have "P \<turnstile>1 \<langle>(Val v, loc)/(E, XS) # exs''',h\<rangle> -\<epsilon>\<rightarrow> \<langle>(inline_call (Val v) (fst (clearInitBlock E XS)), snd (clearInitBlock E XS))/exs''', h\<rangle>"
	  by(rule red1Return) simp
	moreover have "\<not> \<tau>Move1 ((Val v, loc), (E, XS) # exs''')" by auto
	moreover from exec sees Tsvs' have [simp]: "ta = \<epsilon>" "h' = h"
	  and [simp]: "frs' = (v # drop (length vs' + 1) stk'', loc'', C'', M'', pc'' + 1) # frs''"
	  by(auto simp add: compP2_def compMb2_def)
	from sees'' have "P \<turnstile> C sees M: Ts'''\<rightarrow>T''' = meth in C" by(rule sees_method_idemp)
	with sees have [simp]: "T''' = T" by(auto dest: sees_method_fun)
	from call have call': "call (fst (clearInitBlock E XS)) = \<lfloor>(a, M, vs')\<rfloor>" by(simp add: call_clearInitBlock)
	let ?ex' = "(inline_call (Val v) (fst (clearInitBlock E XS)), snd (clearInitBlock E XS))"
	
	from bl' sees'
	have "bisim1_list1 P h ?ex' exs''' None ((v # drop (length vs' + 1) stk'', loc'', C'', M'', pc'' + 1) # frs'')"
	proof(rule bisim1_list1.bl1_Normal)
	  from bisim' have "P,blocks1 (Suc 0) Ts' body',Suc 0,h \<turnstile> (E, XS) \<leftrightarrow> (rev vs' @ Addr a # drop (Suc (length vs')) stk'', loc'', pc'', None)"
	    by(simp add: stk'')
	  with call pc'' show "P,blocks1 (Suc 0) Ts' body',Suc 0,h \<turnstile> ?ex' \<leftrightarrow> (v # drop (length vs' + 1) stk'',loc'',pc'' + 1,None)"
	    by simp (erule (1) bisim1_inline_call_Val, simp)
	next
	  from exsconf'' have "exsconf P h T'' (clearInitBlock E XS)" by(rule exsconf_clearInitBlock)
	  moreover from \<tau>Red1_preserves_sconf[OF wf hconf exsconf red]
	  have "P,h \<turnstile> v :\<le> T" by(auto elim!: exsconf.cases simp add: conf_def)
	  ultimately show "exsconf P h T'' ?ex'" using ha sees''
	    by(auto intro!: exsconf_inline_call_Val[OF wf _ _ _ call'])
	qed(rule hconf)
	ultimately show ?thesis using Red by(fastsimp)
      next
	case True[simp]
	from bl obtain a' vs xs where [simp]: "exs = [(addr a'\<bullet>M(map Val vs), xs)]" 
	  by -(erule bisim1_list.cases, simp_all, fastsimp)
	from exec have [simp]: "h' = h" "ta = \<epsilon>" "frs' = []" by simp_all
	have "P \<turnstile>1 \<langle>(Val v, loc)/[(addr a'\<bullet>M(map Val vs), xs)], h\<rangle> -\<epsilon>\<rightarrow> \<langle>(inline_call (Val v) (fst (clearInitBlock (addr a'\<bullet>M(map Val vs)) xs)), snd (clearInitBlock (addr a'\<bullet>M(map Val vs)) xs))/[], h\<rangle>"
	  by(rule red1Return)(simp_all)
	hence "P \<turnstile>1 \<langle>(Val v, loc)/[(addr a'\<bullet>M(map Val vs), xs)], h\<rangle> -\<epsilon>\<rightarrow> \<langle>(Val v, xs)/[], h\<rangle>" by simp
	thus ?thesis using Red hconf by(fastsimp intro: bl1_finalVal)
      qed }
    moreover {
      assume "\<exists>M n. compE2 body ! pc = Invoke M n"
	and "pc \<noteq> length (compE2 body)"
      with pc obtain M' n where inv: "compE2 body ! pc = Invoke M' n"
	and pc: "pc < length (compE2 body)" by auto
      with bisim1_Invoke_stkD[OF bisim, of M' n] obtain vs v stk' 
	where [simp]: "stk = vs @ v # stk'" "n = length vs" by auto
      from chk sees pc inv have "is_Ref v" by(auto split: split_if_asm simp add: split_beta compP2_def compMb2_def)
      moreover from exec sees pc inv have "v \<noteq> Null" by auto
      ultimately obtain a where [simp]: "v = Addr a" by(auto simp add: is_Ref_def)
      from bisim have "P,blocks1 (Suc 0) Ts body,Suc 0,h \<turnstile> (e, xs) \<leftrightarrow> (rev (rev vs) @ Addr a # stk', loc, pc, None)" by simp
      from bisim1_Invoke_\<tau>Red[OF this, of M'] pc inv len'
      obtain e' xs' where red: "\<tau>Red P h e xs e' xs'"
	and bisim': "P,blocks1 (Suc 0) Ts body,Suc 0,h \<turnstile> clearInitBlock e' xs' \<leftrightarrow> (rev (rev vs) @ Addr a # stk', loc, pc, None)"
	and call': "call e' = \<lfloor>(a, M', rev vs)\<rfloor>" by auto
      from red have Red: "\<tau>Red1 P h ((e, xs), exs) ((e', xs'), exs)" by(rule \<tau>Red_into_\<tau>Red1)
      from exsconf red have exsconf': "exsconf P h T (e', xs')" by(rule \<tau>Red1_preserves_sconf[OF wf hconf])
      with call' obtain arrobj where ha: "h a = \<lfloor>arrobj\<rfloor>"
	and or: "synthesized_call P h (a, M', rev vs) \<or> (\<exists>C fs. h a = \<lfloor>Obj C fs\<rfloor> \<and> P \<turnstile> C has M')"
	by(auto elim!: exsconf.cases dest!: WTrt1_callD)
      from or have ?thesis
      proof
	assume "synthesized_call P h (a, M', rev vs)"
	with exec chk sees pc inv False have False
	  by(auto split: split_if_asm sum.split_asm simp add: split_beta compP2_def compMb2_def has_method_def synthesized_call_conv elim!: is_ArrE)
	thus ?thesis ..
      next
	assume "\<exists>C fs. h a = \<lfloor>Obj C fs\<rfloor> \<and> P \<turnstile> C has M'"
	then obtain C' fs Ts''' T''' body' D' where ha: "h a = \<lfloor>Obj C' fs\<rfloor>"
	  and sees': "P \<turnstile> C' sees M':Ts'''\<rightarrow>T''' = body' in D'" by(fastsimp simp add: has_method_def)
	let ?e = "blocks1 (Suc 0) Ts''' body'"
	let ?xs = "Addr a # rev vs @ replicate (max_vars body') arbitrary"
	let ?e'xs' = "clearInitBlock e' xs'"
	let ?f = "(stk, loc, C, M, pc)"
	let ?f' = "([],[Addr a] @ rev vs @ replicate (max_vars body') arbitrary, D', M', 0)"

	from sees' have iec: "\<not> is_external_call P (Class C') M' (length (rev vs))"
	  by(auto dest: external_call_not_sees_method[OF wf])
	from ha sees' have vsTs''': "length (rev vs) = length Ts'''"
	  using exsconf' call' by(blast elim!: exsconf.cases intro: WTrt_call_sees_length_params[OF wf])
	with call' ha iec sees' have "P \<turnstile>1 \<langle>(e', xs')/exs,h\<rangle> -\<epsilon>\<rightarrow> \<langle>(?e, ?xs)/?e'xs' # exs, h\<rangle>" by(rule red1Call)
	moreover from call' have "\<not> \<tau>Move1 ((e', xs'), exs)" by(auto dest: \<tau>move1_not_call)
	moreover from exec sees ha sees' pc inv have frs': "frs' = ?f' # ?f # FRS" and [simp]: "ta = \<epsilon>" "h' = h"
	  by(auto simp add: split_beta compMb2_def compP2_def split: split_if_asm dest: sees_method_fun external_call_not_sees_method[OF wf])
	from red have xs'xs: "length xs' = length xs" by(rule \<tau>Red_preserves_len)
	with red len' have "Suc (max_vars e') \<le> length xs'" by(auto dest: \<tau>Red_max_vars)
	have "bisim1_list1 P h (?e, ?xs) (?e'xs' # exs) None frs'" unfolding frs'
	proof(rule bisim1_list1.bl1_Normal)
	  from sees' show "P \<turnstile> D' sees M': Ts'''\<rightarrow>T''' = body' in D'" by(rule sees_method_idemp)
	next
	  from call' have "call (fst (clearInitBlock e' xs')) = \<lfloor>(a, M', rev vs)\<rfloor>" by simp	  
	  with bl sees bisim' have "bisim1_list P h D' M' (length (rev vs)) (?e'xs' # exs) ((rev (rev vs) @ Addr a # stk', loc, C, M, pc) # FRS)" using ha sees'
	  proof(rule bl1_Cons)
	    from inv show "compE2 body ! pc = Invoke M' (length (rev vs))" by simp
	  qed(rule exsconf_clearInitBlock[OF exsconf'])
	  with vsTs'''[symmetric] show "bisim1_list P h D' M' (length Ts''') (?e'xs' # exs) (?f # FRS)" by simp
	next
	  from sees_wf_mdecl[OF wf sees'] have "bsok (blocks1 (Suc 0) Ts''' body') (Suc 0)"
	    by(auto simp add: bsok_def wf_mdecl_def intro: WT1_expr_locks WT1_noRetBlock)
	  thus "P,blocks1 (Suc 0) Ts''' body',Suc 0,h \<turnstile> (blocks1 (Suc 0) Ts''' body', Addr a # rev vs @ replicate (max_vars body') arbitrary) \<leftrightarrow> ([], [Addr a] @ rev vs @ replicate (max_vars body') arbitrary, 0, None)"
	    by(auto intro: bisim1_refl)
	next
	  from call_WTrt_vs_conform[OF wf _ sees' _ call'] ha exsconf'
	  have "P,h \<turnstile> rev vs [:\<le>] Ts'''" by(auto elim!: exsconf.cases)
	  with vsTs''' sees' ha sees_method_decl_above[OF sees']
	  show "exsconf P h T''' (blocks1 (Suc 0) Ts''' body', Addr a # rev vs @ replicate (max_vars body') arbitrary)"
	    by(auto simp add: conf_def intro: exsconf_Call[OF wf])
	qed(rule hconf)
	ultimately show ?thesis using Red by(fastsimp)
      qed }
    ultimately show ?thesis by blast
  qed
qed

lemma \<tau>Red1_simulates_exec_1_not_\<tau>:
  assumes wf: "wf_J1_prog P"
  and exec: "exec_1' (compP2 P) (xcp, h, frs) ta (xcp', h', frs')"
  and bisim: "bisim1_list1 P h (e, xs) exs xcp frs"
  and \<tau>: "\<not> \<tau>Move2 P (xcp, h, frs)"
  shows "\<exists>e' xs' exs' ta' e'' xs'' exs''. \<tau>Red1 P h ((e, xs), exs) ((e', xs'), exs') \<and>
                                      P \<turnstile>1 \<langle>(e', xs')/exs', h\<rangle> -ta'\<rightarrow> \<langle>(e'', xs'')/exs'', h'\<rangle> \<and>
                                      \<not> \<tau>Move1 ((e', xs'), exs') \<and> ta_bisim (wbisim1 P) ta' ta \<and>
                                      bisim1_list1 P h' (e'', xs'') exs'' xcp' frs'"
using exec
proof(cases)
  case (exec_1_Normal TA XCP' H' FRS' C M pc H stk loc FRS)
  hence [simp]: "xcp = None" "H = h" "frs = (stk, loc, C, M, pc) # FRS" "TA = ta" "XCP' = xcp'" "H' = h'" "FRS' = frs'"
    by(simp_all)
  note exec = `(TA, XCP', H', FRS') \<in> set (exec_instr (instrs_of (compP2 P) C M ! pc) (compP2 P) H stk loc C M pc FRS)`
  note pc = `pc < length (instrs_of (compP2 P) C M)`
  note check = `check_instr (instrs_of (compP2 P) C M ! pc) (compP2 P) H stk loc C M pc FRS`
  from bisim show ?thesis
  proof(cases)
    case (bl1_Normal C' M' Ts EXS FRS'' T body D ex STK LOC PC XCP)
    hence [simp]: "ex = (e, xs)" "EXS = exs" "STK = stk" "LOC = loc" "C' = C" "M' = M"
      "XCP = xcp" "PC = pc" "FRS'' = FRS" by simp_all
    note sees = `P \<turnstile> C' sees M': Ts\<rightarrow>T = body in D`
    from wf show ?thesis
    proof(rule \<tau>Red_simulates_exec_instr_aux2)
      from \<tau> show "\<not> \<tau>Move2 P (None, h, (stk, loc, C, M, pc) # FRS)" by simp
    next
      show "(ta, xcp', h', frs') \<in> set (exec_instr ((compE2 body @ [Return]) ! pc) (compP2 P) h stk loc C M pc FRS)"
	using exec pc sees by(auto simp add: compP2_def compMb2_def)
    next
      from pc sees show "pc < Suc (length (compE2 body))"
	by(simp add: compP2_def compMb2_def)
    next
      from check sees show "check_instr ((compE2 body @ [Return]) ! pc) (compP2 P) h stk loc C M pc FRS"
	by(simp add: compP2_def compMb2_def)
    next
      from `bisim1_list P h C' M' (length Ts) EXS FRS''`
      show "bisim1_list P h C M (length Ts) exs FRS" by simp
    next
      from sees show "P \<turnstile> C sees M: Ts\<rightarrow>T = body in D" by simp
    next
      from `P,blocks1 (Suc 0) Ts body,Suc 0,h \<turnstile> ex \<leftrightarrow> (STK, LOC, PC, XCP)`
      show "P,blocks1 (Suc 0) Ts body,Suc 0,h \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, None)" by simp
    next
      from `exsconf P h T ex` show "exsconf P h T (e, xs)" by simp
    qed(rule `P \<turnstile> h \<surd>`)
  next
    case bl1_finalVal with exec have False by auto
    thus ?thesis ..
  next
    case bl1_finalThrow with exec have False by auto
    thus ?thesis ..
  qed
next
  case (exec_1_Throw TA \<sigma> a H f FRS)
  hence [simp]: "xcp = \<lfloor>a\<rfloor>" "H = h" "frs = f # FRS" "TA = ta" "\<sigma> = (xcp', h', frs')"
    and xcp_step: "exception_step (compP2 P) (\<epsilon>, \<lfloor>a\<rfloor>, h, f # FRS) = (ta, xcp', h', frs')"
    by simp_all
  from bisim show ?thesis
  proof(cases)
    case (bl1_Normal C' M' Ts EXS FRS'' T body D ex STK LOC PC XCP)
    hence [simp]: "ex = (e, xs)" "EXS = exs" "XCP = xcp" "FRS'' = FRS" "f = (STK, LOC, C', M', PC)"
      and bl: "bisim1_list P h C' M' (length Ts) exs FRS"
      and sees: "P \<turnstile> C' sees M': Ts\<rightarrow>T = body in D"
      and b: "P,blocks1 (Suc 0) Ts body,Suc 0,h \<turnstile> (e, xs) \<leftrightarrow> (STK, LOC, PC, \<lfloor>a\<rfloor>)"
      and exs: "exsconf P h T (e, xs)"
      and hconf: "P \<turnstile> h \<surd>" by simp_all
    from b have PC: "PC < length (compE2 body)" by(auto dest: bisim1_xcpD)
    from sees_method_compP[OF sees, of compMb2] obtain msl mxs ins xt
      where sees2: "compP2 P \<turnstile> C' sees M':Ts\<rightarrow>T = (msl, mxs, compE2 body @ [Return], compxE2 body 0 0) in D"
      by(simp add: compP2_def compMb2_def)
    with \<tau> sees PC have match: "match_ex_table (compP2 P) (cname_of h a) PC (compxE2 body 0 0) = None"
      by -(rule ccontr, auto intro: \<tau>move2xcp intro: ccontr)
    with xcp_step sees2 have [simp]: "ta = \<epsilon>" "xcp' = \<lfloor>a\<rfloor>" "h' = h" "frs' = FRS" by simp_all
    from exs obtain CC TT where wte: "P,[Class CC],h \<turnstile>1 e : TT" and xs: "Suc (max_vars e) \<le> length xs"
      by(auto elim: exsconf.cases)
    from bisim1_WTrt1_Throw_ObjD[OF b wte] obtain CCC fs
      where ha: "h a = \<lfloor>Obj CCC fs\<rfloor>" and subcls: "P \<turnstile> CCC \<preceq>\<^sup>* Throwable" by(auto split: heapobj.split_asm)
    from bisim1_xcp_\<tau>Red[OF ha subcls b, of compMb2] match xs have red: "\<tau>Red P h e xs (Throw a) LOC"
      and b': "P,blocks1 (Suc 0) Ts body,Suc 0,h \<turnstile> (Throw a, LOC) \<leftrightarrow> (STK, LOC, PC, \<lfloor>a\<rfloor>)" by(auto simp add: compP2_def)
    from red have Red: "\<tau>Red1 P h ((e, xs), exs) ((Throw a, LOC), exs)" by(rule \<tau>Red_into_\<tau>Red1)

    show ?thesis
    proof(cases "FRS = []")
      case False
      then obtain F FRS' where [simp]: "FRS = F # FRS'" by(fastsimp simp add: neq_Nil_conv)
      from bl[simplified] obtain vs' E XS EXS' A stk loc C'' M'' pc Ts'' T'' body'' D'' C''' fs''' Ts' T' meth
	where lenvs': "length Ts = length vs'"
	and [simp]: "exs = (E, XS) # EXS'" "F = (rev vs' @ Addr A # stk, loc, C'', M'', pc)"
	and bl'': "bisim1_list P h C'' M'' (length Ts'') EXS' FRS'"
	and sees'': "P \<turnstile> C'' sees M'':Ts''\<rightarrow>T'' = body'' in D''"
	and b'': "P,blocks1 (Suc 0) Ts'' body'',Suc 0,h \<turnstile> (E, XS) \<leftrightarrow> (rev vs' @ Addr A # stk, loc, pc, None)"
	and call'': "call E = \<lfloor>(A, M', vs')\<rfloor>"
	and hA: "h A = \<lfloor>Obj C''' fs'''\<rfloor>"
	and sees''': "P \<turnstile> C''' sees M': Ts'\<rightarrow>T' = meth in C'"
	and inv'': "compE2 body'' ! pc = Invoke M' (length vs')"
	and exs: "exsconf P h T'' (E, XS)"
	by(rule bisim1_list.cases) fastsimp+

      from call'' have "P \<turnstile>1 \<langle>(Throw a, LOC)/(E, XS)#EXS', h\<rangle> -\<epsilon>\<rightarrow> \<langle>(inline_call (Throw a) (fst (clearInitBlock E XS)), snd (clearInitBlock E XS))/EXS', h\<rangle>"
	by(rule red1Return) auto
      moreover have "\<not> \<tau>Move1 ((Throw a, LOC), (E, XS) # EXS')" by auto
      moreover let ?e' = "inline_call (Throw a) (fst (clearInitBlock E XS))"
      let ?xs' = "snd (clearInitBlock E XS)"
      from b'' call'' have "pc < length (compE2 (blocks1 (Suc 0) Ts'' body''))" by(rule bisim1_call_pcD)
      with bisim1_inline_call_Throw[OF b'' call'', of a] inv''
      have bisim''': "P,blocks1 (Suc 0) Ts'' body'',Suc 0,h \<turnstile> (?e', ?xs') \<leftrightarrow> (rev vs' @ Addr A # stk, loc, pc, \<lfloor>a\<rfloor>)" by simp
      from exsconf_clearInitBlock[OF exs] have "exsconf P h T'' (fst (clearInitBlock E XS), snd (clearInitBlock E XS))" by simp
      from exsconf_inline_call_Throw[OF wf hA sees''' this, where a'=a] ha subcls call''
      have "exsconf P h T'' (?e', ?xs')" by(auto simp add: conf_def)
      with bl'' sees'' bisim'''
      have "bisim1_list1 P h (?e', ?xs') EXS' \<lfloor>a\<rfloor> ((rev vs' @ Addr A # stk, loc, C'', M'', pc) # FRS')"
	using hconf by(rule bisim1_list1.bl1_Normal)
      ultimately show ?thesis using Red by(fastsimp)
    next
      case True[simp]
      from bl obtain a' vs xs where [simp]: "exs = [(addr a'\<bullet>M'(map Val vs), xs)]" 
	by -(erule bisim1_list.cases, simp_all, fastsimp)
      from exec have [simp]: "h' = h" "ta = \<epsilon>" "frs' = []" by simp_all
      have "P \<turnstile>1 \<langle>(Throw a, LOC)/[(addr a'\<bullet>M'(map Val vs), xs)], h\<rangle> -\<epsilon>\<rightarrow> \<langle>(inline_call (Throw a) (fst (clearInitBlock (addr a'\<bullet>M'(map Val vs)) xs)), snd (clearInitBlock (addr a'\<bullet>M'(map Val vs)) xs))/[], h\<rangle>"
	by(rule red1Return)(simp_all)
      hence "P \<turnstile>1 \<langle>(Throw a, LOC)/[(addr a'\<bullet>M'(map Val vs), xs)], h\<rangle> -\<epsilon>\<rightarrow> \<langle>(Throw a, xs)/[], h\<rangle>" by simp
      thus ?thesis using Red hconf by(fastsimp intro: bl1_finalThrow)
    qed
  qed simp_all
qed

end