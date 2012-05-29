(*  Title:       Isabelle/Circus
    Author:      Abderrahmane Feliachi, Burkhart Wolff, Marie-Claude Gaudel
                 Univ. Paris-Sud / LRI
    Maintainer:  Abderrahmane Feliachi
*)

theory Denotational_Semantics 
imports Circus_Actions
begin

subsection {* Circus Denotational semantics of actions \label{Denotational}*}

text {* In this subsection, we introduce the definitions of Circus actions denotational semantics.
We provide the proof of well-formedness of every action. We also provide proofs concerning 
the monotonicity of operators over actions.*}

subsubsection {* Stop *}

definition Stop :: "('\<theta>::ev_eq,'\<sigma>) action"
where "Stop \<equiv> action_of (R (true \<turnstile> \<lambda>(A, A'). tr A' = tr A \<and> wait A'))"

lemma Stop_is_action:
"(R (true \<turnstile> \<lambda>(A, A'). tr A' = tr A \<and> wait A')) : action"
apply (simp add: action_def)
apply (rule rd_is_CSP)
by auto

lemmas Stop_is_CSP = Stop_is_action[simplified action_def]

lemma relation_of_Stop:
"relation_of Stop = (R (true \<turnstile> \<lambda>(A, A'). tr A' = tr A \<and> wait A'))"
by (simp add: Stop_def action_of_inverse Stop_is_action)

subsubsection {* Skip *}

definition Skip :: "('\<theta>::ev_eq,'\<sigma>) action" where
"Skip \<equiv> action_of 
                  (R (true \<turnstile> \<lambda>(A, A'). tr A' = tr A \<and> \<not>wait A' \<and> more A = more A'))"

lemma Skip_is_action: 
"(R (true \<turnstile> \<lambda>(A, A'). tr A' = tr A \<and> \<not>wait A' \<and> more A = more A')) : action"
apply (simp add: action_def)
apply (rule rd_is_CSP)
by auto

lemmas Skip_is_CSP = Skip_is_action[simplified action_def]

lemma relation_of_Skip: 
"relation_of Skip = 
                  (R (true \<turnstile> \<lambda>(A, A'). tr A' = tr A \<and> \<not>wait A' \<and> more A = more A'))"
by (simp add: Skip_def action_of_inverse Skip_is_action)

subsubsection {* Chaos *}

definition Chaos :: "('\<theta>::ev_eq,'\<sigma>) action"
where "Chaos \<equiv> action_of (R(false \<turnstile> true))"

lemma Chaos_is_action: "(R(false \<turnstile> true)) : action"
apply (simp add: action_def)
apply (rule rd_is_CSP)
by auto

lemmas Chaos_is_CSP = Chaos_is_action[simplified action_def]

lemma relation_of_Chaos: "relation_of Chaos = (R(false \<turnstile> true))"
by (simp add: Chaos_def action_of_inverse Chaos_is_action)

subsubsection {* Internal choice *}

definition 
Ndet::"('\<theta>::ev_eq,'\<sigma>) action \<Rightarrow> ('\<theta>,'\<sigma>) action \<Rightarrow> ('\<theta>,'\<sigma>) action" (infixl "\<sqinter>" 18) 
where "P \<sqinter> Q \<equiv> action_of ((relation_of P) \<or> (relation_of Q))"

lemma Ndet_is_action: "((relation_of P) \<or> (relation_of Q)) : action"
apply (simp add: action_def)
apply (rule disj_CSP)
apply (simp_all add: relation_of_CSP)
done

lemmas Ndet_is_CSP = Ndet_is_action[simplified action_def]

lemma relation_of_Ndet: "relation_of (P \<sqinter> Q) = ((relation_of P) \<or> (relation_of Q))"
by (simp add: Ndet_def action_of_inverse Ndet_is_action)

lemma mono_Ndet: "mono (op \<sqinter> P)"
by (auto simp: mono_def less_eq_action ref_def relation_of_Ndet)

subsubsection {* External choice *}

definition
Det::"('\<theta>::ev_eq,'\<sigma>) action \<Rightarrow> ('\<theta>,'\<sigma>) action \<Rightarrow> ('\<theta>,'\<sigma>) action" (infixl "[+]" 18)
where "P [+] Q \<equiv> action_of(R((\<not>((relation_of P)\<^isup>f\<^isub>f) \<and> \<not>((relation_of Q)\<^isup>f\<^isub>f)) \<turnstile>
                                             (((relation_of P)\<^isup>t\<^isub>f \<and> ((relation_of Q)\<^isup>t\<^isub>f))
                                                \<triangleleft> \<lambda>(A, A'). tr A = tr A' \<and> wait A' \<triangleright>
                                              ((relation_of P)\<^isup>t\<^isub>f \<or> ((relation_of Q)\<^isup>t\<^isub>f)))))"

notation(xsymbol)
  Det (infixl "\<box>" 18)

lemma Det_is_action: 
"(R((\<not>((relation_of P)\<^isup>f\<^isub>f) \<and> \<not>((relation_of Q)\<^isup>f\<^isub>f)) \<turnstile>
           (((relation_of P)\<^isup>t\<^isub>f \<and> ((relation_of Q)\<^isup>t\<^isub>f))
              \<triangleleft> \<lambda>(A, A'). tr A = tr A' \<and> wait A' \<triangleright>
            ((relation_of P)\<^isup>t\<^isub>f \<or> ((relation_of Q)\<^isup>t\<^isub>f))))) : action"
apply (simp add: action_def spec_def)
apply (rule rd_is_CSP)
apply (auto)
done

lemmas Det_is_CSP = Det_is_action[simplified action_def]

lemma relation_of_Det:
"relation_of (P \<box> Q) = (R((\<not>((relation_of P)\<^isup>f\<^isub>f) \<and> \<not>((relation_of Q)\<^isup>f\<^isub>f)) \<turnstile>
                                          (((relation_of P)\<^isup>t\<^isub>f \<and> ((relation_of Q)\<^isup>t\<^isub>f))
                                             \<triangleleft> \<lambda>(A, A'). tr A = tr A' \<and> wait A' \<triangleright>
                                           ((relation_of P)\<^isup>t\<^isub>f \<or> ((relation_of Q)\<^isup>t\<^isub>f)))))"
apply (unfold Det_def)
apply (rule action_of_inverse)
apply (rule Det_is_action)
done

lemma mono_Det: "mono (op [+] P)"
by (auto simp: mono_def less_eq_action ref_def relation_of_Det design_defs rp_defs fun_eq_iff 
            split: cond_splits dest: relation_of_spec_f_f[simplified] 
                                     relation_of_spec_t_f[simplified])

subsubsection {* Schema expression *}

definition Pre ::"'\<sigma> relation \<Rightarrow> '\<sigma> predicate"
where "Pre sc \<equiv> \<lambda>A. \<exists> A'. sc (A, A')"

definition Schema :: "'\<sigma> relation \<Rightarrow> ('\<theta>::ev_eq,'\<sigma>) action" where
"Schema sc \<equiv> action_of(R ((\<lambda>(A, A'). (Pre sc) (more A)) \<turnstile> 
                           (\<lambda>(A, A'). sc (more A, more A') \<and> \<not>wait A' \<and> tr A = tr A')))"

lemma Schema_is_action: 
"(R ((\<lambda>(A, A'). (Pre sc) (more A)) \<turnstile> 
                 (\<lambda>(A, A'). sc (more A, more A') \<and> \<not>wait A' \<and> tr A = tr A'))) : action"
apply (simp add: action_def)
apply (rule rd_is_CSP)
apply (auto)
done

lemmas Schema_is_CSP = Schema_is_action[simplified action_def]

lemma relation_of_Schema:
"relation_of (Schema sc) = (R ((\<lambda>(A, A'). (Pre sc) (more A)) \<turnstile> 
                          (\<lambda>(A, A'). sc (more A, more A') \<and> \<not>wait A' \<and> tr A = tr A')))"
by (simp add: Schema_def action_of_inverse Schema_is_action)

subsubsection {* Sequential composition *}

definition 
Seq::"('\<theta>::ev_eq,'\<sigma>) action \<Rightarrow> ('\<theta>,'\<sigma>) action \<Rightarrow> ('\<theta>,'\<sigma>) action" (infixl "`;`" 24)
where "P `;` Q \<equiv> action_of (relation_of P ;; relation_of Q)"

lemma Seq_is_action: "(relation_of P ;; relation_of Q) : action"
apply (simp add: action_def)
apply (rule seq_CSP[OF relation_of_CSP[THEN CSP_is_CSP1] relation_of_CSP[THEN CSP_is_R] relation_of_CSP])
done

lemmas Seq_is_CSP = Seq_is_action[simplified action_def]

lemma relation_of_Seq: "relation_of (P `;` Q) = (relation_of P ;; relation_of Q)"
by (simp add: Seq_def action_of_inverse Seq_is_action)

lemma mono_Seq: "mono (op `;` P)"
  by (auto simp: mono_def less_eq_action ref_def relation_of_Seq)

subsubsection {* Parallel composition *}

type_synonym '\<sigma> local_state = "('\<sigma> \<times> ('\<sigma>  \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>))"

fun MergeSt :: "'\<sigma> local_state \<Rightarrow> '\<sigma> local_state \<Rightarrow> ('\<theta>,'\<sigma>) relation_rp" where 
"MergeSt (s1,s1') (s2,s2') = ((\<lambda>(S, S'). (s1' s1) (more S) = more S');; 
                            (\<lambda>(S::('\<theta>,'\<sigma>) alphabet_rp, S'). (s2' s2) (more S) = more S'))"

definition listCons ::"'\<theta> \<Rightarrow> '\<theta> list list \<Rightarrow> '\<theta> list list" ("_ ## _") where
"a ## l = ((map (Cons a)) l)"

fun ParMergel :: "'\<theta>::ev_eq list \<Rightarrow> '\<theta> list \<Rightarrow> '\<theta> set \<Rightarrow> '\<theta> list list" where
    "ParMergel [] [] cs = [[]]"
  | "ParMergel [] (b#tr2) cs = (if (filter_chan_set b cs) then [[]]
                                          else (b ## (ParMergel [] tr2 cs)))" 
  | "ParMergel (a#tr1) [] cs = (if (filter_chan_set a cs) then [[]]
                                          else (a ## (ParMergel tr1 [] cs)))"
  | "ParMergel (a#tr1) (b#tr2) cs = 
           (if (filter_chan_set a cs)
                   then (if (ev_eq a b) 
                              then (a ## (ParMergel tr1 tr2 cs)) 
                               else (if (filter_chan_set b cs) 
                                        then [[]] 
                                         else (b ## (ParMergel (a#tr1) tr2 cs))))
                     else (if (filter_chan_set b cs) 
                               then (a ## (ParMergel tr1 (b#tr2) cs)) 
                                 else (a ## (ParMergel tr1 (b#tr2) cs)) 
                                            @ (b ## (ParMergel (a#tr1) tr2 cs))))"

definition ParMerge::"'\<theta>::ev_eq list \<Rightarrow> '\<theta> list \<Rightarrow> '\<theta> set \<Rightarrow> '\<theta> list set" where
"ParMerge tr1 tr2 cs = set (ParMergel tr1 tr2 cs)"

definition M_par::"(('\<theta>::ev_eq), '\<sigma>) alpha_rp_scheme \<Rightarrow> ('\<sigma>  \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>)
                            \<Rightarrow> ('\<theta>, '\<sigma>) alpha_rp_scheme \<Rightarrow> ('\<sigma> \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>)
                                \<Rightarrow> ('\<theta> set) \<Rightarrow> ('\<theta>, '\<sigma>) relation_rp" where
"M_par s1 x1 s2 x2 cs = 
((\<lambda>(S, S'). ((diff_tr S' S) \<in> ParMerge (diff_tr s1 S) (diff_tr s2 S) cs \<and>
     ev_eq (tr_filter (tr s1) cs) (tr_filter (tr s2) cs))) \<and>
   ((\<lambda>(S, S'). (wait s1 \<or> wait s2) \<and> 
                             ref S' \<subseteq> ((((ref s1)\<union>(ref s2))\<inter>cs)\<union>(((ref s1)\<inter>(ref s2))-cs)))
   \<triangleleft> wait o snd \<triangleright>
   ((\<lambda>(S, S'). (\<not>wait s1 \<or> \<not>wait s2)) \<and> MergeSt ((more s1), x1) ((more s2), x2))))"

definition  Par::"('\<theta>::ev_eq,'\<sigma>) action \<Rightarrow> 
                    ('\<sigma>  \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>) \<Rightarrow> '\<theta> set \<Rightarrow> ('\<sigma>  \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>) \<Rightarrow> 
                    ('\<theta>,'\<sigma>) action \<Rightarrow> ('\<theta>,'\<sigma>) action" ("_ \<lbrakk> _ | _ | _ \<rbrakk> _") where
"A1 \<lbrakk> ns1 | cs | ns2 \<rbrakk> A2 \<equiv> (action_of (R ((\<lambda> (S, S'). 
 \<not> (\<exists> tr1 tr2. ((relation_of A1)\<^isup>f\<^isub>f ;; (\<lambda> (S, S'). tr1 = (tr S))) (S, S') 
 \<and> (spec False (wait S) (relation_of A2) ;; (\<lambda> (S, _). tr2 = (tr S))) (S, S')
 \<and> ((tr_filter tr1 cs) = (tr_filter tr2 cs))) \<and>
 \<not> (\<exists> tr1 tr2. (spec False (wait S) (relation_of A1);;(\<lambda>(S, _). tr1 = tr S)) (S, S')
 \<and> ((relation_of A2)\<^isup>f\<^isub>f ;; (\<lambda>(S, S'). tr2 = (tr S))) (S, S') 
 \<and> ((tr_filter tr1 cs) = (tr_filter tr2 cs)))) \<turnstile> 
   (\<lambda> (S, S'). (\<exists> s1 s2. ((\<lambda> (A, A'). (relation_of A1)\<^isup>t\<^isub>f (A, s1)
 \<and> ((relation_of A2)\<^isup>t\<^isub>f (A, s2)));; M_par s1 ns1 s2 ns2 cs) (S, S'))))))"

lemma Par_is_action: "(R ((\<lambda> (S, S'). 
 \<not> (\<exists> tr1 tr2. ((relation_of A1)\<^isup>f\<^isub>f ;; (\<lambda> (S, S'). tr1 = (tr S))) (S, S') 
 \<and> (spec False (wait S) (relation_of A2) ;; (\<lambda> (S, S'). tr2 = (tr S))) (S, S')
 \<and> ((tr_filter tr1 cs) = (tr_filter tr2 cs))) \<and>
 \<not> (\<exists> tr1 tr2. (spec False (wait S) (relation_of A1);;(\<lambda>(S, _). tr1 = tr S)) (S, S')
 \<and> ((relation_of A2)\<^isup>f\<^isub>f ;; (\<lambda> (S, S'). tr2 = (tr S))) (S, S') 
 \<and> ((tr_filter tr1 cs) = (tr_filter tr2 cs)))) \<turnstile> 
   (\<lambda> (S, S'). (\<exists> s1 s2. ((\<lambda> (A, A'). (relation_of A1)\<^isup>t\<^isub>f (A, s1)
 \<and> ((relation_of A2)\<^isup>t\<^isub>f (A, s2)));; M_par s1 ns1 s2 ns2 cs) (S, S'))))) : action"
apply (simp add: action_def)
apply (rule rd_is_CSP)
apply (blast)
done

lemmas Par_is_CSP = Par_is_action[simplified action_def]

lemma relation_of_Par:
"relation_of (A1 \<lbrakk> ns1 | cs | ns2 \<rbrakk> A2) = (R ((\<lambda> (S, S'). 
 \<not> (\<exists> tr1 tr2. ((relation_of A1)\<^isup>f\<^isub>f ;; (\<lambda> (S, S'). tr1 = (tr S))) (S, S') 
 \<and> (spec False (wait S) (relation_of A2) ;; (\<lambda> (S, S'). tr2 = (tr S))) (S, S') 
 \<and> ((tr_filter tr1 cs) = (tr_filter tr2 cs))) \<and>
 \<not> (\<exists> tr1 tr2. (spec False (wait S) (relation_of A1);;(\<lambda>(S, _). tr1 = tr S)) (S, S') 
 \<and> ((relation_of A2)\<^isup>f\<^isub>f ;; (\<lambda> (S, S'). tr2 = (tr S))) (S, S') 
 \<and> ((tr_filter tr1 cs) = (tr_filter tr2 cs)))) \<turnstile> 
   (\<lambda> (S, S'). (\<exists> s1 s2. ((\<lambda> (A, A'). (relation_of A1)\<^isup>t\<^isub>f (A, s1)
 \<and> ((relation_of A2)\<^isup>t\<^isub>f (A, s2)));; M_par s1 ns1 s2 ns2 cs) (S, S')))))"
apply (unfold Par_def)
apply (rule action_of_inverse)
apply (rule Par_is_action)
done

lemma mono_Par: "mono (\<lambda>Q. P \<lbrakk> ns1 | cs | ns2 \<rbrakk> Q)"
  apply (auto simp: mono_def less_eq_action ref_def relation_of_Par design_defs fun_eq_iff rp_defs
              split: cond_splits)
  apply (auto simp: rp_defs dest: relation_of_spec_f_f[simplified] relation_of_spec_t_f[simplified])
  apply (erule_tac x="tr ba" in allE, auto)
  apply (erule notE)
  apply (auto dest: relation_of_spec_f_f relation_of_spec_t_f)
done

subsubsection {* Assignment *}
text {* Circus variables are represented by a stack (list) of values. 
they are characterized by two functions, $select$ and $update$.
The Circus variable type is defined as a tuple ($select$ * $update$) with a 
list of values instead of a single value. *}

type_synonym ('a, '\<sigma>) var_list = "('\<sigma> \<Rightarrow> 'a list) * (('a list \<Rightarrow> 'a list) \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>)"

text {* The $select$ function returns the top value of the stack. *}

definition select :: "('a, 'r) var_list \<Rightarrow> 'r \<Rightarrow> 'a"
where "select f \<equiv> \<lambda> A. hd ((fst f) A)"

text {* The $increase$ function pushes a new value to the top of the stack. *}

definition increase :: "('a, 'r) var_list \<Rightarrow> 'a \<Rightarrow> 'r \<Rightarrow> 'r"
where "increase f val \<equiv> (snd f) (\<lambda> l. val#l)"

text {* The $decrease$ function pops the top value of the stack. *}

definition decrease :: "('a, 'r) var_list \<Rightarrow> 'r \<Rightarrow> 'r"
where "decrease f \<equiv> (snd f) (\<lambda> l. (tl l))"

text {* The $update$ function updates the top value of the stack. *}

definition update :: "('a, 'r) var_list \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'r \<Rightarrow> 'r"
where "update f upd \<equiv> (snd f) (\<lambda> l. (upd (hd l))#(tl l))"

text {* The $update0$ function initializes the top of the stack with an arbitrary value. *}

definition update0 :: "('a, 'r) var_list \<Rightarrow> 'r \<Rightarrow> 'r"
where "update0 f \<equiv> (snd f) (\<lambda> l. ((SOME upd. True) (hd l))#(tl l))"

text {* The $VAR-LIST$ function allows to retrieve a Circus variable from its name.*}

syntax "_VAR_LIST" :: "id \<Rightarrow> ('a, 'r) var_list"  ("VAR'_LIST _")
translations "VAR_LIST x" => "(x, _update_name x)"

definition ASSIGN::"('v, '\<sigma>) var_list \<Rightarrow> ('\<sigma> \<Rightarrow> 'v) \<Rightarrow> ('\<theta>::ev_eq, '\<sigma>) action" where
"ASSIGN x e \<equiv> action_of (R (true \<turnstile> (\<lambda> (S, S'). tr S' = tr S \<and> \<not>wait S' \<and> 
                                 (more S' = (update x (\<lambda>_. (e (more S)))) (more S)))))"

syntax "_assign"::"id \<Rightarrow> ('\<sigma> \<Rightarrow> 'v) \<Rightarrow> ('\<theta>, '\<sigma>) action"  ("_ `:=` _")
translations "y `:=` vv" => "CONST ASSIGN (VAR y) vv"

lemma Assign_is_action: 
"(R (true \<turnstile> (\<lambda> (S, S'). tr S' = tr S \<and> \<not>wait S' \<and> 
                (more S' = (update x (\<lambda>_. (e (more S)))) (more S))))) : action"
apply (simp add: action_def)
apply (rule rd_is_CSP)
apply (blast)
done

lemmas Assign_is_CSP = Assign_is_action[simplified action_def]

lemma relation_of_Assign:
"relation_of (ASSIGN x e) = (R (true \<turnstile> (\<lambda> (S, S'). tr S' = tr S \<and> \<not>wait S' \<and> 
                                   (more S' = (update x (\<lambda>_. (e (more S)))) (more S)))))"
by (simp add: ASSIGN_def action_of_inverse Assign_is_action)

subsubsection {* Variable scope *}

definition Var::"('v, '\<sigma>) var_list \<Rightarrow>('\<theta>, '\<sigma>) action \<Rightarrow> ('\<theta>::ev_eq,'\<sigma>) action" where
"Var v A \<equiv> action_of(
     (R(true \<turnstile> (\<lambda> (A, A'). (\<exists> x. A' = A\<lparr>more := (increase v x (more A))\<rparr>))));; 
     relation_of A;; 
     (R(true \<turnstile> (\<lambda> (A, A'). A' = A\<lparr>more := (decrease v (more A))\<rparr>))))"

syntax "_var"::"idt \<Rightarrow> ('\<theta>, '\<sigma>) action \<Rightarrow> ('\<theta>, '\<sigma>) action" ("var _ \<bullet> _" [1000] 999)
translations "var y \<bullet> Act" => "CONST Var (VAR_LIST y) Act"

lemma Var_is_action:
"((R(true \<turnstile> (\<lambda> (A, A'). (\<exists> x. A' = A\<lparr>more := (increase v x (more A))\<rparr>))));;
  relation_of A;; 
  (R(true \<turnstile> (\<lambda> (A, A'). A' = A\<lparr>more := (decrease v (more A))\<rparr>)))) : action"
  apply (simp add: action_def)
  apply (rule seq_CSP)
  prefer 3
  apply (rule seq_CSP)
  apply (auto simp: relation_of_CSP1 relation_of_R)
  apply (rule rd_is_CSP)
  apply (auto simp: csp_defs rp_defs design_defs fun_eq_iff prefix_def increase_def decrease_def
               split: cond_splits)
done

lemmas Var_is_CSP = Var_is_action[simplified action_def]

lemma relation_of_Var:
"relation_of (Var v A) = 
    ((R(true \<turnstile> (\<lambda> (A, A'). (\<exists> x. A' = A\<lparr>more := (increase v x (more A))\<rparr>))));; 
     relation_of A;; 
     (R(true \<turnstile> (\<lambda> (A, A'). A' = A\<lparr>more := (decrease v (more A))\<rparr>))))"
by (simp add: Var_def action_of_inverse Var_is_action)

lemma mono_Var : "mono (Var x)"
  by (auto simp: mono_def less_eq_action ref_def relation_of_Var)

subsubsection {* Guarded action *}

definition Guard::"'\<sigma> predicate \<Rightarrow> ('\<theta>::ev_eq, '\<sigma>) action \<Rightarrow> ('\<theta>, '\<sigma>) action" ("_ `&` _")
where "g `&` P \<equiv> action_of(R (((g o more o fst) \<longrightarrow> \<not> ((relation_of P)\<^isup>f\<^isub>f)) \<turnstile> 
                             (((g o more o fst) \<and> ((relation_of P)\<^isup>t\<^isub>f)) \<or> 
                         ((\<not>(g o more o fst)) \<and> (\<lambda> (A, A'). tr A' = tr A \<and> wait A')))))"

lemma Guard_is_action: 
"(R ( ((g o more o fst) \<longrightarrow> \<not> ((relation_of P)\<^isup>f\<^isub>f)) \<turnstile> 
                (((g o more o fst) \<and> ((relation_of P)\<^isup>t\<^isub>f)) \<or> 
                 ((\<not>(g o more o fst)) \<and> (\<lambda> (A, A'). tr A' = tr A \<and> wait A'))))) : action"
  by (auto simp add: action_def spec_def intro: rd_is_CSP)

lemmas Guard_is_CSP = Guard_is_action[simplified action_def]

lemma relation_of_Guard:
"relation_of (g `&` P) = (R (((g o more o fst) \<longrightarrow>  \<not> ((relation_of P)\<^isup>f\<^isub>f)) \<turnstile> 
                             (((g o more o fst) \<and> ((relation_of P)\<^isup>t\<^isub>f)) \<or>
                          ((\<not>(g o more o fst)) \<and> (\<lambda> (A, A'). tr A' = tr A \<and> wait A')))))"
  apply (unfold Guard_def)
  apply (subst action_of_inverse)
  apply (simp_all only: Guard_is_action)
done

lemma mono_Guard : "mono (Guard g)"
  apply (auto simp: mono_def less_eq_action ref_def rp_defs design_defs relation_of_Guard 
                split: cond_splits)
  apply (auto dest: relation_of_spec_f_f relation_of_spec_t_f)
done

lemma false_Guard: "false `&` P = Stop"
apply (subst relation_of_inject[symmetric])
apply (subst relation_of_Stop)
apply (subst relation_of_Guard)
apply (simp add: fun_eq_iff utp_defs csp_defs design_defs rp_defs)
done

lemma false_Guard1: "\<And> a b. g (alpha_rp.more a) = False \<Longrightarrow> 
                                (relation_of (g `&` P)) (a, b) = (relation_of Stop) (a, b)"
apply (subst relation_of_Guard)
apply (subst relation_of_Stop)
apply (auto simp: fun_eq_iff csp_defs design_defs rp_defs split: cond_splits)
done

lemma true_Guard: "true `&` P = P"
apply (subst relation_of_inject[symmetric])
apply (subst relation_of_Guard)
apply (subst CSP_is_rd[OF relation_of_CSP]) back back
apply (simp add: fun_eq_iff utp_defs csp_defs design_defs rp_defs)
done

lemma true_Guard1: "\<And> a b. g (alpha_rp.more a) = True \<Longrightarrow> 
                                     (relation_of (g `&` P)) (a, b) = (relation_of P) (a, b)"
apply (subst relation_of_Guard)
apply (subst CSP_is_rd[OF relation_of_CSP]) back back
apply (auto simp: fun_eq_iff csp_defs design_defs rp_defs split: cond_splits)
done

subsubsection {* Prefixed action *}

definition do where
"do e \<equiv> (\<lambda>(A, A'). tr A = tr A' \<and> e \<notin> (ref A')) \<triangleleft> wait o fst \<triangleright> 
                                                              (\<lambda>(A, A'). tr A' = (tr A @[e]))"

definition do_I::"('v \<Rightarrow> '\<theta>) \<Rightarrow> ('v, '\<sigma>) var_list \<Rightarrow> 'v set \<Rightarrow> ('\<theta>, '\<sigma>) relation_rp"
where "do_I c x P \<equiv>  ((\<lambda>(A, A'). tr A = tr A' \<and> (c`P) \<inter> (ref A') = {})
                                \<triangleleft> wait o fst \<triangleright> 
  (\<lambda>(A, A'). hd (tr A' - tr A) \<in> (c`P) \<and> (c (select x (more A)) = (last (tr A')))))"

definition
Prefix::"('v \<Rightarrow> '\<theta>) \<Rightarrow> ('v, '\<sigma>) var_list \<Rightarrow> 'v set \<Rightarrow> ('\<theta>::ev_eq, '\<sigma>) action 
                                                                           \<Rightarrow> ('\<theta>, '\<sigma>) action" where
"Prefix c x S P \<equiv> action_of(R(true \<turnstile> (do_I c x S) \<and> 
                                                    (\<lambda> (A, A'). more A' = more A)))`;` P"

definition Prefix0::"'\<theta> \<Rightarrow> ('\<theta>::ev_eq, '\<sigma>) action \<Rightarrow> ('\<theta>, '\<sigma>) action" where
"Prefix0 c P \<equiv> action_of(R(true \<turnstile> (do c) \<and> (\<lambda> (A, A'). more A' = more A)))`;` P"

definition 
read::"('v \<Rightarrow> '\<theta>) \<Rightarrow> ('v, '\<sigma>) var_list \<Rightarrow> ('\<theta>::ev_eq, '\<sigma>) action \<Rightarrow> ('\<theta>, '\<sigma>) action"
where  "read c x P  \<equiv> Prefix c x UNIV P"

definition 
write1::"('v \<Rightarrow> '\<theta>) \<Rightarrow> ('\<sigma> \<Rightarrow> 'v) \<Rightarrow> ('\<theta>::ev_eq, '\<sigma>) action \<Rightarrow> ('\<theta>, '\<sigma>) action"
where "write1 c a P \<equiv> Prefix c (\<lambda> s. [a s], (\<lambda> x. \<lambda>y. y)) UNIV P"

definition 
write0::"'\<theta> \<Rightarrow> ('\<theta>::ev_eq, '\<sigma>) action \<Rightarrow> ('\<theta>, '\<sigma>) action" 
where "write0 c P \<equiv> Prefix0 c P"

syntax
"_read"  ::"[id, pttrn, ('\<theta>, '\<sigma>) action] => ('\<theta>, '\<sigma>) action" ("(_`?`_ /\<rightarrow> _)")
"_readS" ::"[id, pttrn, '\<theta> set,('\<theta>, '\<sigma>) action] => ('\<theta>, '\<sigma>) action" ("(_`?`_`:`_ /\<rightarrow> _)")
"_write" ::"[id, '\<sigma>, ('\<theta>, '\<sigma>) action] => ('\<theta>, '\<sigma>) action" ("(_`!`_ /\<rightarrow> _)")
"_writeS"::"['\<theta>, ('\<theta>, '\<sigma>) action] => ('\<theta>, '\<sigma>) action" ("(_ /\<rightarrow> _)")

translations
"_read c p P"    == "CONST read c (VAR_LIST p) P" 
"_readS c p b P" == "CONST Prefix c (VAR_LIST p) b P"
"_write c p P"   == "CONST write1 c p P"  
"_writeS a P"    == "CONST write0 a P"

lemma Prefix_is_action:
"(R(true \<turnstile> (do_I c x S) \<and> (\<lambda> (A, A'). more A' = more A))) : action"
by (auto simp add: action_def intro: rd_is_CSP)

lemma Prefix0_is_action:
"(R(true \<turnstile> (do c) \<and> (\<lambda> (A, A'). more A' = more A))) : action"
by (auto simp add: action_def intro: rd_is_CSP)

lemmas Prefix_is_CSP = Prefix_is_action[simplified action_def]

lemmas Prefix0_is_CSP = Prefix0_is_action[simplified action_def]

lemma relation_of_Prefix:
"relation_of (Prefix c x S P) = 
((R(true \<turnstile> (do_I c x S) \<and> (\<lambda> (A, A'). more A' = more A)));; relation_of P)"
by (simp add: Prefix_def relation_of_Seq action_of_inverse Prefix_is_action)

lemma relation_of_Prefix0:
"relation_of (Prefix0 c P) = 
((R(true \<turnstile> (do c) \<and> (\<lambda> (A, A'). more A' = more A)));; relation_of P)"
by (simp add: Prefix0_def relation_of_Seq action_of_inverse Prefix0_is_action)

lemma mono_Prefix : "mono (Prefix c x s)"
by (auto simp: mono_def less_eq_action ref_def relation_of_Prefix)

lemma mono_Prefix0 : "mono(Prefix0 c)"
by (auto simp: mono_def less_eq_action ref_def relation_of_Prefix0)

subsubsection {* Hiding *}

definition Hide::"('\<theta>::ev_eq, '\<sigma>) action \<Rightarrow> '\<theta> set \<Rightarrow> ('\<theta>, '\<sigma>) action" (infixl "\\" 18) where
"P \\ cs \<equiv> action_of(R(\<lambda>(S, S'). \<exists> s. (diff_tr S' S) = (tr_filter (s - (tr S)) cs) \<longrightarrow>
             (relation_of P)(S, S'\<lparr>tr := s, ref := (ref S') \<union> cs \<rparr>));; (relation_of Skip))"

(* Definition of Hide modified : to check in the semantics with Ana and Jim, *)
(* who use a slightly stronger definition (which is unlikely to be invariant) *)

lemma Hide_is_not_CSP: 
"is_CSP_process (R(\<lambda>(S, S'). \<exists> s. (diff_tr S' S) = (tr_filter (s - (tr S)) cs) \<and> 
        (relation_of P)(S, S'\<lparr>tr := s, ref := (ref S') \<union> cs \<rparr>)) ;; (relation_of Skip))"
apply (rule seq_CSP)
prefer 3
apply (rule relation_of_CSP)
apply (auto simp: csp_defs rp_defs design_defs diff_tr_def prefix_def fun_eq_iff split: cond_splits)
apply (subst CSP_is_rd, auto simp: rp_defs relation_of_CSP design_defs fun_eq_iff split: cond_splits)
oops

lemma Hide_is_action: 
"(R(\<lambda>(S, S'). \<exists> s. (diff_tr S' S) = (tr_filter (s - (tr S)) cs) \<longrightarrow>
   (relation_of P)(S, S'\<lparr>tr := s, ref := (ref S') \<union> cs \<rparr>));; (relation_of Skip)) : action"
  apply (simp add: action_def)
  apply (rule seq_CSP)
  prefer 3
  apply (rule relation_of_CSP)
  apply (simp add: rp_defs design_defs fun_eq_iff csp_defs, auto split: cond_splits)
  apply (subst CSP_is_rd, auto simp: rp_defs relation_of_CSP design_defs fun_eq_iff split: cond_splits)
done

lemmas Hide_is_CSP = Hide_is_action[simplified action_def]

lemma relation_of_Hide:
"relation_of (P \\ cs) = (R(\<lambda>(S, S'). \<exists> s. (diff_tr S' S) = (tr_filter (s - (tr S)) cs)
        \<longrightarrow> (relation_of P)(S, S'\<lparr>tr :=s, ref := (ref S') \<union> cs \<rparr>));; (relation_of Skip))"
  by (simp add: Hide_def action_of_inverse Hide_is_action)

lemma mono_Hide : "mono(\<lambda> P. P \\ cs)"
by (auto simp: mono_def less_eq_action ref_def prefix_def utp_defs relation_of_Hide rp_defs)

subsubsection {* Recursion \label{subsec:Recursion}*}

text {* To represent the recursion operator "@{text \<mu>}" over actions, we use the
universal least fix-point operator "@{const lfp}" defined in the HOL library for lattices. 
The operator "@{const lfp}" is inherited from the "Complete Lattice class" under some conditions. 
All theorems defined over this operator can be reused. *}

text {* In the @{theory Circus_Actions} theory, we presented the proof that Circus actions 
form a complete lattice. The Knaster-Tarski Theorem (in its simplest formulation) states 
that any monotone function on a complete lattice has a least fixed-point. 
This is a consequence of the basic boundary properties of the complete lattice operations. 
Instantiating the complete lattice class allows one to inherit these properties with the 
definition of the least fixed-point for monotonic functions over Circus actions.
 *}

syntax "_MU"::"[idt, idt \<Rightarrow> ('\<theta>, '\<sigma>) action] \<Rightarrow> ('\<theta>, '\<sigma>) action"  ("\<mu> _ \<bullet> _")
translations "_MU X P" == "CONST lfp (\<lambda> X. P)"


(*<*)
text{* Instead fo the following: *}
lemma is_action_REP_Mu:
  shows "is_CSP_process (relation_of (lfp P))"
oops 

text{* ... we refer to the proof of @{thm Sup_is_action} and its 
analogue who capture the essence of this proof at the level of the
type instantiation. *}

text{* Monotonicity: STATUS: probably critical.  Does not seem to be necessary for 
parameterless Circus. *}
lemma mono_Mu:
  assumes A : "mono P"
  and     B : "\<And> X. mono (P X)"
  shows  "mono (lfp P)"
apply (subst lfp_unfold)
apply (auto simp: A B)
done 

(*>*)
end
