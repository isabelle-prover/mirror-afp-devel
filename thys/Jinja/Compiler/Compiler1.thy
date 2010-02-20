(*  Title:      Jinja/Compiler/Compiler1.thy
    ID:         $Id: Compiler1.thy,v 1.4 2008-11-06 15:48:09 nipkow Exp $
    Author:     Tobias Nipkow
    Copyright   TUM 2003
*)

header {* \isaheader{Compilation Stage 1} *}

theory Compiler1 imports PCompiler J1 ListIndex2 begin

text{* Replacing variable names by indices. *}

consts
  compE\<^isub>1  :: "vname list \<Rightarrow> expr      \<Rightarrow> expr\<^isub>1"
  compEs\<^isub>1 :: "vname list \<Rightarrow> expr list \<Rightarrow> expr\<^isub>1 list"

primrec
"compE\<^isub>1 Vs (new C) = new C"
"compE\<^isub>1 Vs (Cast C e) = Cast C (compE\<^isub>1 Vs e)"
"compE\<^isub>1 Vs (Val v) = Val v"
"compE\<^isub>1 Vs (e\<^isub>1 \<guillemotleft>bop\<guillemotright> e\<^isub>2) = (compE\<^isub>1 Vs e\<^isub>1) \<guillemotleft>bop\<guillemotright> (compE\<^isub>1 Vs e\<^isub>2)"
"compE\<^isub>1 Vs (Var V) = Var(last_index Vs V)"
"compE\<^isub>1 Vs (V:=e) = (last_index Vs V):= (compE\<^isub>1 Vs e)"
"compE\<^isub>1 Vs (e\<bullet>F{D}) = (compE\<^isub>1 Vs e)\<bullet>F{D}"
"compE\<^isub>1 Vs (e\<^isub>1\<bullet>F{D}:=e\<^isub>2) = (compE\<^isub>1 Vs e\<^isub>1)\<bullet>F{D} := (compE\<^isub>1 Vs e\<^isub>2)"
"compE\<^isub>1 Vs (e\<bullet>M(es)) = (compE\<^isub>1 Vs e)\<bullet>M(compEs\<^isub>1 Vs es)"
"compE\<^isub>1 Vs {V:T; e} = {(size Vs):T; compE\<^isub>1 (Vs@[V]) e}"
"compE\<^isub>1 Vs (e\<^isub>1;;e\<^isub>2) = (compE\<^isub>1 Vs e\<^isub>1);;(compE\<^isub>1 Vs e\<^isub>2)"
"compE\<^isub>1 Vs (if (e) e\<^isub>1 else e\<^isub>2) = if (compE\<^isub>1 Vs e) (compE\<^isub>1 Vs e\<^isub>1) else (compE\<^isub>1 Vs e\<^isub>2)"
"compE\<^isub>1 Vs (while (e) c) = while (compE\<^isub>1 Vs e) (compE\<^isub>1 Vs c)"
"compE\<^isub>1 Vs (throw e) = throw (compE\<^isub>1 Vs e)"
"compE\<^isub>1 Vs (try e\<^isub>1 catch(C V) e\<^isub>2) =
    try(compE\<^isub>1 Vs e\<^isub>1) catch(C (size Vs)) (compE\<^isub>1 (Vs@[V]) e\<^isub>2)"

"compEs\<^isub>1 Vs []     = []"
"compEs\<^isub>1 Vs (e#es) = compE\<^isub>1 Vs e # compEs\<^isub>1 Vs es"

lemma [simp]: "compEs\<^isub>1 Vs es = map (compE\<^isub>1 Vs) es"
(*<*)by(induct es type:list) simp_all(*>*)


consts
  fin\<^isub>1:: "expr \<Rightarrow> expr\<^isub>1"
primrec
  "fin\<^isub>1(Val v) = Val v"
  "fin\<^isub>1(throw e) = throw(fin\<^isub>1 e)"

lemma comp_final: "final e \<Longrightarrow> compE\<^isub>1 Vs e = fin\<^isub>1 e"
(*<*)by(erule finalE, simp_all)(*>*)


lemma [simp]:
      "\<And>Vs. max_vars (compE\<^isub>1 Vs e) = max_vars e"
and "\<And>Vs. max_varss (compEs\<^isub>1 Vs es) = max_varss es"
(*<*)by (induct e and es) simp_all(*>*)


text{* Compiling programs: *}

constdefs
  compP\<^isub>1 :: "J_prog \<Rightarrow> J\<^isub>1_prog"
  "compP\<^isub>1  \<equiv>  compP (\<lambda>(pns,body). compE\<^isub>1 (this#pns) body)"

(*<*)
declare compP\<^isub>1_def[simp]
(*>*)

end
