(*  Title:      JinjaThreads/Compiler/Compiler1.thy
    Author:     Andreas Lochbihler, Tobias Nipkow

    Based on Jinja/Compiler/Compiler1
*)

header {* \isaheader{Compilation Stage 1} *}

theory Compiler1 imports
  PCompiler
  J1State
  ListIndex 
begin

definition fresh_var :: "vname list \<Rightarrow> vname"
where "fresh_var Vs \<equiv> Aux.concat (STR ''V'' # Vs)"

lemma fresh_var_fresh: "fresh_var Vs \<notin> set Vs"
proof -
  have "\<forall>V \<in> set Vs. length (explode V) < length (explode (fresh_var Vs))"
    by(induct Vs)(auto simp add: fresh_var_def Aux.concat_def STR_inverse implode_def)
  thus ?thesis by auto
qed

text{* Replacing variable names by indices. *}

primrec compE1  :: "vname list \<Rightarrow> expr      \<Rightarrow> expr1"
  and compEs1 :: "vname list \<Rightarrow> expr list \<Rightarrow> expr1 list"
where
  "compE1 Vs (new C) = new C"
| "compE1 Vs (newA T\<lfloor>e\<rceil>) = newA T\<lfloor>compE1 Vs e\<rceil>"
| "compE1 Vs (Cast T e) = Cast T (compE1 Vs e)"
| "compE1 Vs (e instanceof T) = (compE1 Vs e) instanceof T"
| "compE1 Vs (Val v) = Val v"
| "compE1 Vs (Var V) = Var(index Vs V)"
| "compE1 Vs (e\<guillemotleft>bop\<guillemotright>e') = (compE1 Vs e)\<guillemotleft>bop\<guillemotright>(compE1 Vs e')"
| "compE1 Vs (V:=e) = (index Vs V):= (compE1 Vs e)"
| "compE1 Vs (a\<lfloor>i\<rceil>) = (compE1 Vs a)\<lfloor>compE1 Vs i\<rceil>"
| "compE1 Vs (a\<lfloor>i\<rceil>:=e) = (compE1 Vs a)\<lfloor>compE1 Vs i\<rceil>:=compE1 Vs e"
| "compE1 Vs (a\<bullet>length) = compE1 Vs a\<bullet>length"
| "compE1 Vs (e\<bullet>F{D}) = compE1 Vs e\<bullet>F{D}"
| "compE1 Vs (e\<bullet>F{D}:=e') = compE1 Vs e\<bullet>F{D}:=compE1 Vs e'"
| "compE1 Vs (e\<bullet>M(es)) = (compE1 Vs e)\<bullet>M(compEs1 Vs es)"
| "compE1 Vs {V:T=vo; e} = {(size Vs):T=vo; compE1 (Vs@[V]) e}"
| "compE1 Vs (sync\<^bsub>U\<^esub> (o') e) = sync\<^bsub>length Vs\<^esub> (compE1 Vs o') (compE1 (Vs@[fresh_var Vs]) e)"
| "compE1 Vs (insync\<^bsub>U\<^esub> (a) e) = insync\<^bsub>length Vs\<^esub> (a) (compE1 (Vs@[fresh_var Vs]) e)"
| "compE1 Vs (e1;;e2) = (compE1 Vs e1);;(compE1 Vs e2)"
| "compE1 Vs (if (b) e1 else e2) = (if (compE1 Vs b) (compE1 Vs e1) else (compE1 Vs e2))"
| "compE1 Vs (while (b) e) = (while (compE1 Vs b) (compE1 Vs e))"
| "compE1 Vs (throw e) = throw (compE1 Vs e)"
| "compE1 Vs (try e1 catch(C V) e2) = try(compE1 Vs e1) catch(C (size Vs)) (compE1 (Vs@[V]) e2)"

| "compEs1 Vs []     = []"
| "compEs1 Vs (e#es) = compE1 Vs e # compEs1 Vs es"

lemma compEs1_conv_map [simp]: "compEs1 Vs es = map (compE1 Vs) es"
by(induct es) simp_all

lemmas compEs1_map_Val = compEs1_conv_map

lemma compE1_eq_Val [simp]: "compE1 Vs e = Val v \<longleftrightarrow> e = Val v"
apply(cases e, auto)
done

lemma Val_eq_compE1 [simp]: "Val v = compE1 Vs e \<longleftrightarrow> e = Val v"
apply(cases e, auto)
done

lemma compEs1_eq_map_Val [simp]: "compEs1 Vs es = map Val vs \<longleftrightarrow> es = map Val vs"
apply(induct es arbitrary: vs)
apply(auto, blast)
done

lemma compE1_eq_Var [simp]: "compE1 Vs e = Var V \<longleftrightarrow> (\<exists>V'. e = Var V' \<and> V = index Vs V')"
by(cases e, auto)

lemma compE1_eq_Call [simp]:
  "compE1 Vs e = obj\<bullet>M(params) \<longleftrightarrow> (\<exists>obj' params'. e = obj'\<bullet>M(params') \<and> compE1 Vs obj' = obj \<and> compEs1 Vs params' = params)"
by(cases e, auto)

lemma length_compEs2 [simp]:
  "length (compEs1 Vs es) = length es"
by(simp add: compEs1_conv_map)

lemma expr_locks_compE1 [simp]: "expr_locks (compE1 Vs e) = expr_locks e"
  and expr_lockss_compEs1 [simp]: "expr_lockss (compEs1 Vs es) = expr_lockss es"
by(induct e and es arbitrary: Vs and Vs)(auto intro: ext)

lemma contains_insync_compE1 [simp]: "contains_insync (compE1 Vs e) = contains_insync e"
  and contains_insyncs_compEs1 [simp]: "contains_insyncs (compEs1 Vs es) = contains_insyncs es"
by(induct e and es arbitrary: Vs and Vs)simp_all

lemma max_vars_compE1: "max_vars (compE1 Vs e) = max_vars e"
  and max_varss_compEs1: "max_varss (compEs1 Vs es) = max_varss es"
apply(induct e and es arbitrary: Vs and Vs)
apply(auto)
done

lemma \<B>: "size Vs = n \<Longrightarrow> \<B> (compE1 Vs e) n"
and \<B>s: "size Vs = n \<Longrightarrow> \<B>s (compEs1 Vs es) n"
apply(induct e and es arbitrary: Vs n and Vs n)
apply auto
done

lemma fv_compE1: "fv e \<subseteq> set Vs \<Longrightarrow> fv (compE1 Vs e) = (index Vs) ` (fv e)"
  and fvs_compEs1: "fvs es \<subseteq> set Vs \<Longrightarrow> fvs (compEs1 Vs es) = (index Vs) ` (fvs es)"
proof(induct e and es arbitrary: Vs and Vs)
  case (Block V ty vo exp)
  have IH: "\<And>Vs. fv exp \<subseteq> set Vs \<Longrightarrow> fv (compE1 Vs exp) = index Vs ` fv exp" by fact
  from `fv {V:ty=vo; exp} \<subseteq> set Vs` have fv': "fv exp \<subseteq> set (Vs @ [V])" by auto
  from IH[OF this] have IH': "fv (compE1 (Vs @ [V]) exp) = index (Vs @ [V]) ` fv exp" .
  have "fv (compE1 (Vs @ [V]) exp) - {length Vs} = index Vs ` (fv exp - {V})"
  proof(rule equalityI[OF subsetI subsetI])
    fix x
    assume x: "x \<in> fv (compE1 (Vs @ [V]) exp) - {length Vs}"
    hence "x \<noteq> length Vs" by simp
    from x IH' have "x \<in> index (Vs @ [V]) ` fv exp" by simp
    thus "x \<in> index Vs ` (fv exp - {V})"
    proof(rule imageE)
      fix y
      assume [simp]: "x = index (Vs @ [V]) y"
	and y: "y \<in> fv exp"
      have "y \<noteq> V"
      proof
	assume [simp]: "y = V"
	hence "x = length Vs" by simp
	with `x \<noteq> length Vs` show False by contradiction
      qed
      moreover with fv' y have "y \<in> set Vs" by auto
      ultimately have "index (Vs @ [V]) y = index Vs y" by(simp)
      thus ?thesis using y `y \<noteq> V` by auto
    qed
  next
    fix x
    assume x: "x \<in> index Vs ` (fv exp - {V})"
    thus "x \<in> fv (compE1 (Vs @ [V]) exp) - {length Vs}"
    proof(rule imageE)
      fix y
      assume [simp]: "x = index Vs y"
	and y: "y \<in> fv exp - {V}"
      with fv' have "y \<in> set Vs" "y \<noteq> V" by auto
      hence "index Vs y = index (Vs @ [V]) y" by simp
      with y have "x \<in> index (Vs @ [V]) ` fv exp" by auto
      thus ?thesis using IH' `y \<in> set Vs` by simp
    qed
  qed
  thus ?case by simp
next
  case (Synchronized V exp1 exp2)
  have IH1: "\<And>Vs. fv exp1 \<subseteq> set Vs \<Longrightarrow> fv (compE1 Vs exp1) = index Vs ` fv exp1" 
    and IH2: "\<And>Vs. fv exp2 \<subseteq> set Vs \<Longrightarrow> fv (compE1 Vs exp2) = index Vs ` fv exp2" by fact+
  from `fv (sync\<^bsub>V\<^esub> (exp1) exp2) \<subseteq> set Vs` have fv1: "fv exp1 \<subseteq> set Vs"
    and fv2: "fv exp2 \<subseteq> set Vs" by auto
  from fv2 have fv2': "fv exp2 \<subseteq> set (Vs @ [fresh_var Vs])" by auto
  have "index (Vs @ [fresh_var Vs]) ` fv exp2 = index Vs ` fv exp2"
  proof(rule equalityI[OF subsetI subsetI])
    fix x
    assume x: "x \<in> index (Vs @ [fresh_var Vs]) ` fv exp2"
    thus "x \<in> index Vs ` fv exp2"
    proof(rule imageE)
      fix y
      assume [simp]: "x = index (Vs @ [fresh_var Vs]) y"
	and y: "y \<in> fv exp2"
      from y fv2 have "y \<in> set Vs" by auto
      moreover hence "y \<noteq> (fresh_var Vs)" by(auto simp add: fresh_var_fresh)
      ultimately show ?thesis using y by(auto)
    qed
  next
    fix x
    assume x: "x \<in> index Vs ` fv exp2"
    thus "x \<in> index (Vs @ [fresh_var Vs]) ` fv exp2"
    proof(rule imageE)
      fix y
      assume [simp]: "x = index Vs y"
	and y: "y \<in> fv exp2"
      from y fv2 have "y \<in> set Vs" by auto
      moreover hence "y \<noteq> (fresh_var Vs)" by(auto simp add: fresh_var_fresh)
      ultimately have "index Vs y = index (Vs @ [fresh_var Vs]) y" by simp
      thus ?thesis using y by(auto)
    qed
  qed
  with IH1[OF fv1] IH2[OF fv2'] show ?case by(auto)
next
  case (InSynchronized V a exp)
  have IH: "\<And>Vs. fv exp \<subseteq> set Vs \<Longrightarrow> fv (compE1 Vs exp) = index Vs ` fv exp" by fact
  from `fv (insync\<^bsub>V\<^esub> (a) exp) \<subseteq> set Vs` have fv: "fv exp \<subseteq> set Vs" by simp
  hence fv': "fv exp \<subseteq> set (Vs @ [fresh_var Vs])" by auto
  have "index (Vs @ [fresh_var Vs]) ` fv exp = index Vs ` fv exp"
  proof(rule equalityI[OF subsetI subsetI])
    fix x
    assume "x \<in> index (Vs @ [fresh_var Vs]) ` fv exp"
    thus "x \<in> index Vs ` fv exp"
    proof(rule imageE)
      fix y
      assume [simp]: "x = index (Vs @ [fresh_var Vs]) y"
	and y: "y \<in> fv exp"
      from y fv have "y \<in> set Vs" by auto
      moreover hence "y \<noteq> (fresh_var Vs)" by(auto simp add: fresh_var_fresh)
      ultimately have "index (Vs @ [fresh_var Vs]) y = index Vs y" by simp
      thus ?thesis using y by simp
    qed
  next
    fix x
    assume "x \<in> index Vs ` fv exp"
    thus "x \<in> index (Vs @ [fresh_var Vs]) ` fv exp"
    proof(rule imageE)
      fix y
      assume [simp]: "x = index Vs y"
	and y: "y \<in> fv exp"
      from y fv have "y \<in> set Vs" by auto
      moreover hence "y \<noteq> (fresh_var Vs)" by(auto simp add: fresh_var_fresh)
      ultimately have "index Vs y = index (Vs @ [fresh_var Vs]) y" by simp
      thus ?thesis using y by auto
    qed
  qed
  with IH[OF fv'] show ?case by simp
next
  case (TryCatch exp1 C V exp2)
  have IH1: "\<And>Vs. fv exp1 \<subseteq> set Vs \<Longrightarrow> fv (compE1 Vs exp1) = index Vs ` fv exp1" 
    and IH2: "\<And>Vs. fv exp2 \<subseteq> set Vs \<Longrightarrow> fv (compE1 Vs exp2) = index Vs ` fv exp2" by fact+
  from `fv (try exp1 catch(C V) exp2) \<subseteq> set Vs` have fv1: "fv exp1 \<subseteq> set Vs"
    and fv2: "fv exp2 \<subseteq> set (Vs @ [V])" by auto
  have "index (Vs @ [V]) ` fv exp2 - {length Vs} = index Vs ` (fv exp2 - {V})" 
  proof(rule equalityI[OF subsetI subsetI])
    fix x
    assume x: "x \<in> index (Vs @ [V]) ` fv exp2 - {length Vs}"
    hence "x \<noteq> length Vs" by simp
    from x have "x \<in> index (Vs @ [V]) ` fv exp2" by auto
    thus "x \<in> index Vs ` (fv exp2 - {V})"
    proof(rule imageE)
      fix y
      assume [simp]: "x = index (Vs @ [V]) y"
	and y: "y \<in> fv exp2"
      have "y \<noteq> V"
      proof
	assume [simp]: "y = V"
	hence "x = length Vs" by simp
	with `x \<noteq> length Vs` show False by contradiction
      qed
      moreover with fv2 y have "y \<in> set Vs" by auto
      ultimately have "index (Vs @ [V]) y = index Vs y" by(simp)
      thus ?thesis using y `y \<noteq> V` by auto
    qed
  next
    fix x
    assume x: "x \<in> index Vs ` (fv exp2 - {V})"
    thus "x \<in> index (Vs @ [V]) ` fv exp2 - {length Vs}"
    proof(rule imageE)
      fix y
      assume [simp]: "x = index Vs y"
	and y: "y \<in> fv exp2 - {V}"
      with fv2 have "y \<in> set Vs" "y \<noteq> V" by auto
      hence "index Vs y = index (Vs @ [V]) y" by simp
      with y have "x \<in> index (Vs @ [V]) ` fv exp2" by auto
      thus ?thesis using `y \<in> set Vs` by simp
    qed
  qed
  with IH1[OF fv1] IH2[OF fv2] show ?case by auto
qed(auto)

lemma syncvars_compE1: "fv e \<subseteq> set Vs \<Longrightarrow> syncvars (compE1 Vs e)"
  and syncvarss_compEs1: "fvs es \<subseteq> set Vs \<Longrightarrow> syncvarss (compEs1 Vs es)"
proof(induct e and es arbitrary: Vs and Vs)
  case (Block V ty vo exp)
  from `fv {V:ty=vo; exp} \<subseteq> set Vs` have "fv exp \<subseteq> set (Vs @ [V])" by auto
  from `\<And>Vs. fv exp \<subseteq> set Vs \<Longrightarrow> syncvars (compE1 Vs exp)`[OF this] show ?case by(simp)
next
  case (Synchronized V exp1 exp2)
  note IH1 = `\<And>Vs. fv exp1 \<subseteq> set Vs \<Longrightarrow> syncvars (compE1 Vs exp1)`
  note IH2 = `\<And>Vs. fv exp2 \<subseteq> set Vs \<Longrightarrow> syncvars (compE1 Vs exp2)`
  from `fv (sync\<^bsub>V\<^esub> (exp1) exp2) \<subseteq> set Vs` have fv1: "fv exp1 \<subseteq> set Vs"
    and fv2: "fv exp2 \<subseteq> set Vs" and fv2': "fv exp2 \<subseteq> set (Vs @ [fresh_var Vs])" by auto
  have "length Vs \<notin> index (Vs @ [fresh_var Vs]) ` fv exp2"
  proof
    assume "length Vs \<in> index (Vs @ [fresh_var Vs]) ` fv exp2"
    thus False
    proof(rule imageE)
      fix x
      assume x: "length Vs = index (Vs @ [fresh_var Vs]) x"
	and x': "x \<in> fv exp2"
      from x' fv2 have "x \<in> set Vs" "x \<noteq> (fresh_var Vs)" by(auto simp add: fresh_var_fresh)
      with x show ?thesis by(simp)
    qed
  qed
  with IH1[OF fv1] IH2[OF fv2'] fv2' show ?case by(simp add: fv_compE1)
next
  case (InSynchronized V a exp)
  note IH = `\<And>Vs. fv exp \<subseteq> set Vs \<Longrightarrow> syncvars (compE1 Vs exp)`
  from `fv (insync\<^bsub>V\<^esub> (a) exp) \<subseteq> set Vs` have fv: "fv exp \<subseteq> set Vs"
    and fv': "fv exp \<subseteq> set (Vs @ [fresh_var Vs])" by auto
  have "length Vs \<notin> index (Vs @ [fresh_var Vs]) ` fv exp"
  proof
    assume "length Vs \<in> index (Vs @ [fresh_var Vs]) ` fv exp"
    thus False
    proof(rule imageE)
      fix x
      assume x: "length Vs = index (Vs @ [fresh_var Vs]) x"
	and x': "x \<in> fv exp"
      from x' fv have "x \<in> set Vs" "x \<noteq> (fresh_var Vs)" by(auto simp add: fresh_var_fresh)
      with x show ?thesis by(simp)
    qed
  qed
  with IH[OF fv'] fv' show ?case by(simp add: fv_compE1)
next
  case (TryCatch exp1 C V exp2)
  note IH1 = `\<And>Vs. fv exp1 \<subseteq> set Vs \<Longrightarrow> syncvars (compE1 Vs exp1)`
  note IH2 = `\<And>Vs. fv exp2 \<subseteq> set Vs \<Longrightarrow> syncvars (compE1 Vs exp2)`
  from `fv (try exp1 catch(C V) exp2) \<subseteq> set Vs` have fv1: "fv exp1 \<subseteq> set Vs"
    and fv2: "fv exp2 \<subseteq> set (Vs @ [V])" by auto
  from IH1[OF fv1] IH2[OF fv2] show ?case by auto
qed auto

lemma (in heap_base) synthesized_call_compP [simp]:
  "synthesized_call (compP f P) h aMvs = synthesized_call P h aMvs"
by(simp add: synthesized_call_def)


primrec fin1 :: "expr \<Rightarrow> expr1"
where
  "fin1 (Val v) = Val v"
| "fin1 (throw e) = throw (fin1 e)"

lemma comp_final: "final e \<Longrightarrow> compE1 Vs e = fin1 e"
by(erule finalE, simp_all)

lemma [simp]: "max_vars (compE1 Vs e) = max_vars e"
  and "max_varss (compEs1 Vs es) = max_varss es"
by (induct e and es arbitrary: Vs and Vs)(simp_all)

text{* Compiling programs: *}

definition compP1 :: "J_prog \<Rightarrow> J1_prog"
where
  "compP1  \<equiv>  compP (\<lambda>C M Ts T (pns,body). compE1 (this#pns) body)"

declare compP1_def[simp]

end
