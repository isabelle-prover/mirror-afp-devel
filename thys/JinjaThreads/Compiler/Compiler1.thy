(*  Title:      JinjaThreads/Compiler/Compiler1.thy
    Author:     Andreas Lochbihler, Tobias Nipkow

    Based on Jinja/Compiler/Compiler1
*)

header {* \isaheader{Compilation Stage 1} *}

theory Compiler1 imports
  PCompiler
  J1
  ListIndex 
begin

definition fresh_var :: "vname list \<Rightarrow> vname"
where "fresh_var Vs \<equiv> Aux.concat (STR ''V'' # Vs)"

lemma fresh_var_fresh: "fresh_var Vs \<notin> set Vs"
proof -
  have "\<forall>V \<in> set Vs. length (explode V) < length (explode (fresh_var Vs))"
    by(induct Vs)(auto simp add: fresh_var_def Aux.concat_def explode_def implode_def)
  thus ?thesis by auto
qed

text{* Replacing variable names by indices. *}

consts
  compE1  :: "vname list \<Rightarrow> expr      \<Rightarrow> expr1"
  compEs1 :: "vname list \<Rightarrow> expr list \<Rightarrow> expr1 list"

primrec
"compE1 Vs (new C) = new C"
"compE1 Vs (newA T\<lfloor>e\<rceil>) = newA T\<lfloor>compE1 Vs e\<rceil>"
"compE1 Vs (Cast T e) = Cast T (compE1 Vs e)"
"compE1 Vs (Val v) = Val v"
"compE1 Vs (Var V) = Var(index Vs V)"
"compE1 Vs (e\<guillemotleft>bop\<guillemotright>e') = (compE1 Vs e)\<guillemotleft>bop\<guillemotright>(compE1 Vs e')"
"compE1 Vs (V:=e) = (index Vs V):= (compE1 Vs e)"
"compE1 Vs (a\<lfloor>i\<rceil>) = (compE1 Vs a)\<lfloor>compE1 Vs i\<rceil>"
"compE1 Vs (a\<lfloor>i\<rceil>:=e) = (compE1 Vs a)\<lfloor>compE1 Vs i\<rceil>:=compE1 Vs e"
"compE1 Vs (a\<bullet>length) = compE1 Vs a\<bullet>length"
"compE1 Vs (e\<bullet>F{D}) = compE1 Vs e\<bullet>F{D}"
"compE1 Vs (e\<bullet>F{D}:=e') = compE1 Vs e\<bullet>F{D}:=compE1 Vs e'"
"compE1 Vs (e\<bullet>M(es)) = (compE1 Vs e)\<bullet>M(compEs1 Vs es)"
"compE1 Vs {V:T=vo; e} = {(size Vs):T=vo; compE1 (Vs@[V]) e}"
"compE1 Vs (sync\<^bsub>U\<^esub> (o') e) = sync\<^bsub>length Vs\<^esub> (compE1 Vs o') (compE1 (Vs@[fresh_var Vs]) e)"
"compE1 Vs (insync\<^bsub>U\<^esub> (a) e) = insync\<^bsub>length Vs\<^esub> (a) (compE1 (Vs@[fresh_var Vs]) e)"
"compE1 Vs (e1;;e2) = (compE1 Vs e1);;(compE1 Vs e2)"
"compE1 Vs (if (b) e1 else e2) = (if (compE1 Vs b) (compE1 Vs e1) else (compE1 Vs e2))"
"compE1 Vs (while (b) e) = (while (compE1 Vs b) (compE1 Vs e))"
"compE1 Vs (throw e) = throw (compE1 Vs e)"
"compE1 Vs (try e1 catch(C V) e2) = try(compE1 Vs e1) catch(C (size Vs)) (compE1 (Vs@[V]) e2)"

"compEs1 Vs []     = []"
"compEs1 Vs (e#es) = compE1 Vs e # compEs1 Vs es"

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

lemma synthesized_call_compP [simp]:
  "synthesized_call (compP f P) h aMvs = synthesized_call P h aMvs"
by(simp add: synthesized_call_def)


consts
  fin1 :: "expr \<Rightarrow> expr1"
primrec
  "fin1 (Val v) = Val v"
  "fin1 (throw e) = throw (fin1 e)"

lemma comp_final: "final e \<Longrightarrow> compE1 Vs e = fin1 e"
by(erule finalE, simp_all)

lemma [simp]: "max_vars (compE1 Vs e) = max_vars e"
  and "max_varss (compEs1 Vs es) = max_varss es"
by (induct e and es arbitrary: Vs and Vs)(simp_all)

text{* Compiling programs: *}

constdefs
  compP1 :: "J_prog \<Rightarrow> J1_prog"
  "compP1  \<equiv>  compP (\<lambda>(pns,body). compE1 (this#pns) body)"

declare compP1_def[simp]

end
