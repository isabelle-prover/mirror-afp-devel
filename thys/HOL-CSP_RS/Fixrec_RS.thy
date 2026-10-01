(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSP_Metric_Space - Seeing Processes as a Metric Space
 *
 * Author          : Benoît Ballenghien, Burkhart Wolff
 *
 * This file       : Conceptual tests of the generic Fixrec package, RS instance
 *
 * Copyright (c) 2025 Université Paris-Saclay, France
 ******************************************************************************\<close>
(*>*)

chapter \<open>Conceptual Tests: the Restriction-Space Instance of \<^verbatim>\<open>Fixrec\<close>\<close>

theory Fixrec_RS
  imports "GenFixrec-RS"
begin

text \<open>The tests are organised by concept and mirror the theory \<^verbatim>\<open>Fixrec_HOLCF\<close>. Expected
failures are checked by \<open>expect_failure\<close>, which runs the command semantics on the current
theory and asserts that it fails with a message containing a given fragment.\<close>

ML \<open>
fun expect_failure langs vars eqns fragment =
  let val spec = (map (fn (n, T) => (Binding.name n, SOME T, NoSyn)) vars,
                  map (fn (n, e) => (false, ((Binding.name n, []), e))) eqns)
      val msg_of = Protocol_Message.clean_output o Runtime.exn_message
  in case Exn.result (GenFixrec.add_fixrec_langs_global (map (rpair Position.none) langs) spec)
                     (Context.the_global_context ()) of
       Exn.Res _   => error ("expected failure, but Fixrec succeeded: " ^ commas langs)
     | Exn.Exn exn => if String.isSubstring fragment (msg_of exn) then ()
                      else error ("unexpected failure message:\n" ^ msg_of exn)
  end
\<close>


section \<open>Language Selection\<close>

text \<open>A language that always fails to prove the fixpoint unfolding; used to test fallback.\<close>

setup \<open>fn thy => Context.Theory thy
   |> GenFixrec.update_language (Binding.make ("BROKEN", \<^here>))
        {mk_fix = #mk_fix RS_instance.rs, dest_fix = #dest_fix RS_instance.rs, lambda' = #lambda' RS_instance.rs,
         apply = #apply RS_instance.rs, shift_tac = #shift_tac RS_instance.rs, fix_tac = K no_tac,
         proj_tac = #proj_tac RS_instance.rs, fixind_tac = #fixind_tac RS_instance.rs}
   |> Context.the_theory\<close>

text \<open>Explicit selection:\<close>
Fixrec [RS] l2 :: \<open>int process\<close> where l2_eq : \<open>l2 = 2 \<rightarrow> l2\<close>

text \<open>Languages are tried from left to right; the first one that succeeds is taken:\<close>
Fixrec [BROKEN, RS] l3 :: \<open>int process\<close> where l3_eq : \<open>l3 = 3 \<rightarrow> l3\<close>

ML \<open>
val proc = "int process"
(* the default language HOLCF is not available in this instance *)
val _ = expect_failure ["HOLCF"] [("e0", proc)] [("e0_eq", "e0 = 1 \<rightarrow> e0")]
                       "Undefined Fixrec language: \"HOLCF\""
(* all languages fail: every failure is reported *)
val _ = expect_failure ["BROKEN"] [("e1", proc)] [("e1_eq", "e1 = 1 \<rightarrow> e1")]
                       "no language succeeded"
(* unknown and misspelled (case-sensitive) language names *)
val _ = expect_failure ["FOO"] [("e2", proc)] [("e2_eq", "e2 = 1 \<rightarrow> e2")]
                       "Undefined Fixrec language: \"FOO\""
val _ = expect_failure ["rs"] [("e3", proc)] [("e3_eq", "e3 = 1 \<rightarrow> e3")]
                       "Undefined Fixrec language: \"rs\""
val _ = expect_failure [] [("e4", proc)] [("e4_eq", "e4 = 1 \<rightarrow> e4")]
                       "no language given"
\<close>


section \<open>Unshifted Equations\<close>

Fixrec [RS] u1 :: \<open>int \<Rightarrow> int process\<close> where u1_eq : \<open>u1 = (\<lambda>x. x \<rightarrow> u1 (x+1))\<close>


section \<open>Generic Shift over HOL Application\<close>

text \<open>The shift over HOL application is provided by the core, independently of the language;
no continuous function space is required.\<close>

Fixrec [RS] s1 :: \<open>int \<Rightarrow> int process\<close> where s1_eq : \<open>s1 x = x \<rightarrow> s1 (x+1)\<close>
Fixrec [RS] s2 :: \<open>int \<Rightarrow> nat \<Rightarrow> int process\<close> where s2_eq : \<open>s2 x n = x \<rightarrow> s2 (x+1) (Suc n)\<close>
Fixrec [RS] s3 :: \<open>int \<times> nat \<Rightarrow> int process\<close> where s3_eq : \<open>s3 (x,n) = x \<rightarrow> s3 (x+1,n)\<close>
Fixrec [RS] s4 :: \<open>int \<times> int \<times> int \<Rightarrow> int process\<close> where s4_eq : \<open>s4 (x,y,z) = x \<rightarrow> s4 (y,z,x)\<close>
Fixrec [RS] s5 :: \<open>int \<times> nat \<Rightarrow> bool \<times> int \<Rightarrow> int process\<close>
  where s5_eq : \<open>s5 (x,n) (b,y) = x \<rightarrow> s5 (y,Suc n) (\<not>b,x)\<close>

text \<open>The shift is equivalent to the unshifted form:\<close>
lemma \<open>s1 = (\<lambda>x. x \<rightarrow> s1 (x+1))\<close> using s1_eq by blast

ML \<open>
val _ = expect_failure ["RS"] [("e5", "int \<Rightarrow> int process")] [("e5_eq", "e5 0 = 0 \<rightarrow> e5 0")]
                       "args must be free variables or tuples of them"
val _ = expect_failure ["RS"] [("e6", "int \<Rightarrow> int process")] 
                       [("e6_eq", "(if True then e6 else e6) x = x \<rightarrow> e6 x")]
                       "lhs head must be one of the declared constants"
\<close>


section \<open>Domain-Specific Shift\<close>

text \<open>The restriction-space instance has no application/abstraction pair of its own; a lhs
using the HOLCF application \<open>\<cdot>\<close> is not recognised:\<close>

ML \<open>
val _ = expect_failure ["RS"] [("e7", "int process \<rightarrow> int process")] [("e7_eq", "e7\<cdot>P = 1 \<rightarrow> e7\<cdot>P")]
                       "lhs head must be one of the declared constants"
\<close>


section \<open>Mutual Recursion\<close>

Fixrec [RS] m1 :: \<open>int \<Rightarrow> int process\<close> and m2 :: \<open>int \<Rightarrow> int process\<close>
  where m1_eq : \<open>m1 x = 1 \<rightarrow> m2 x\<close>
  |     m2_eq : \<open>m2 x = 2 \<rightarrow> m1 (x+1)\<close>

Fixrec [RS] m3 :: \<open>int \<Rightarrow> int process\<close> and m4 :: \<open>int process\<close>
  where m3_eq : \<open>m3 x = x \<rightarrow> m4\<close>
  |     m4_eq : \<open>m4 = 0 \<rightarrow> m3 1\<close>


text \<open>Equations that are not (self-)recursive, alone or within a system:\<close>
Fixrec [RS] n1 :: \<open>int \<Rightarrow> int process\<close> where n1_eq : \<open>n1 x = x \<rightarrow> Skip\<close>
Fixrec [RS] n2 :: \<open>int \<Rightarrow> int process\<close> and n3 :: \<open>int \<Rightarrow> int process\<close>
  where n2_eq : \<open>n2 x = x \<rightarrow> n3 x\<close>
  |     n3_eq : \<open>n3 x = x \<rightarrow> n3 (x+1)\<close>


text \<open>A larger mutual system (guarded equations, choices, finite non-determinism, a member
that is not self-recursive):\<close>
Fixrec [RS] t1 :: \<open>int \<Rightarrow> int process\<close> and t2 :: \<open>int \<Rightarrow> int process\<close>
  and t3 :: \<open>int \<Rightarrow> int process\<close> and t4 :: \<open>int process\<close> and t5 :: \<open>int \<Rightarrow> int process\<close>
  where t1_eq : \<open>t1 x = 1 \<rightarrow> t2 x\<close>
  |     t2_eq : \<open>t2 x = (2 \<rightarrow> t3 x) \<box> (3 \<rightarrow> t1 (x+1))\<close>
  |     t3_eq : \<open>t3 x = (\<sqinter> a \<in> {0..x}. a \<rightarrow> t4)\<close>
  |     t4_eq : \<open>t4 = 0 \<rightarrow> t5 1\<close>
  |     t5_eq : \<open>t5 x = (x \<rightarrow> t1 x) \<sqinter> (x \<rightarrow> t4)\<close>


text \<open>Recursion through the continuation of the exception operator \<open>\<Theta>\<close> (FDR's \<open>[| A |>\<close>),
also when the exception event is initial (as in the crash handling of Dali):\<close>
Fixrec [RS] cr :: \<open>int process\<close> and cr' :: \<open>int process\<close>
  where cr_eq  : \<open>cr  = ((1 \<rightarrow> Skip) ||| (0 \<rightarrow> Skip)) \<Theta> a \<in> {0}. cr'\<close>
  |     cr'_eq : \<open>cr' = ((2 \<rightarrow> Skip) ||| (0 \<rightarrow> Skip)) \<Theta> a \<in> {0}. cr'\<close>

text \<open>Recursion in both operands of \<open>\<Theta>\<close> (guarded in the left one), with a parametrised
continuation:\<close>
Fixrec [RS] tb :: \<open>int \<Rightarrow> int process\<close>
  where tb_eq : \<open>tb x = (x \<rightarrow> tb (x+1) ||| (0 \<rightarrow> Skip)) \<Theta> a \<in> {0}. tb (x-1)\<close>


section \<open>Polymorphism\<close>

Fixrec [RS] p1 :: \<open>'a \<Rightarrow> 'a process\<close> where p1_eq : \<open>p1 x = x \<rightarrow> p1 x\<close>

Fixrec [RS] p2 :: \<open>'a \<Rightarrow> 'a process\<close> and p3 :: \<open>'a \<Rightarrow> 'a process\<close>
  where p2_eq : \<open>p2 x = x \<rightarrow> p3 x\<close>
  |     p3_eq : \<open>p3 x = x \<rightarrow> p2 x\<close>

lemma \<open>p1 x = x \<rightarrow> p1 x\<close> by (fact p1_eq)

text \<open>Type variables are of sort \<open>type\<close>, not \<open>cpo\<close>/\<open>domain\<close>:\<close>
lemma \<open>p1 (n::nat) = n \<rightarrow> p1 n\<close> by (fact p1_eq)


section \<open>Generated Theorems\<close>

thm m1_m2_rec_def m1_m2_rec_unfold m1_def m2_def m1_eq m2_eq m1_m2_induct

lemma \<open>s5 (x,n) (b,y) = x \<rightarrow> s5 (y,Suc n) (\<not>b,x)\<close> by (fact s5_eq)

text \<open>Fixpoint induction over the restriction fixpoint: admissibility, an arbitrary start
value, step.\<close>

ML \<open>
val _ = @{assert} (Thm.nprems_of @{thm s1_induct} = 3)
val _ = @{assert} (Thm.nprems_of @{thm m1_m2_induct} = 3)
\<close>


text \<open>Unlike HOLCF's \<^verbatim>\<open>fixrec\<close>, the equations are \<^emph>\<open>not\<close> simp rules by default (unguarded use
of recursive equations by the simplifier loops); \<open>[simp]\<close> declares them explicitly:\<close>

Fixrec [RS] sa :: \<open>int \<Rightarrow> int process\<close> where sa_eq : \<open>sa x = x \<rightarrow> Skip\<close>
Fixrec [RS] sb :: \<open>int \<Rightarrow> int process\<close> where sb_eq [simp] : \<open>sb x = x \<rightarrow> Skip\<close>

lemma \<open>sb 1 = 1 \<rightarrow> Skip\<close> by simp

ML \<open>
val _ = @{assert} (is_none (try (Goal.prove \<^context> [] [] @{prop \<open>sa 1 = 1 \<rightarrow> Skip\<close>})
                                (fn {context, ...} => asm_full_simp_tac context 1)))
\<close>

section \<open>Semantic Properties of the Instance\<close>

text \<open>In restriction spaces, the fixpoint exists only for constructive (guarded) equations;
an unguarded equation is rejected:\<close>

ML \<open>
val _ = expect_failure ["RS"] [("d1", "int \<Rightarrow> int process")] [("d1_eq", "d1 x = d1 (x+1)")]
                       "constructive"
\<close>


section \<open>Local Contexts: Locales, Contexts, Interpretation\<close>

text \<open>\<^verbatim>\<open>Fixrec\<close> is a local-theory command: it can be used inside locales and other local
contexts. Locale parameters may occur in the equations; the generated constants are
abstracted over the parameters they depend on, and all theorems are available under
interpretation.\<close>

locale L1 = fixes k :: int assumes k_pos : \<open>0 < k\<close>
begin
Fixrec [RS] r1 :: \<open>int \<Rightarrow> int process\<close> where r1_eq : \<open>r1 x = x \<rightarrow> r1 (x + k)\<close>
Fixrec [RS] r2 :: \<open>int \<Rightarrow> int process\<close> and r3 :: \<open>int process\<close>
  where r2_eq : \<open>r2 x = x \<rightarrow> r3\<close>
  |     r3_eq : \<open>r3 = k \<rightarrow> r2 k\<close>
lemma \<open>r1 x = x \<rightarrow> r1 (x + k)\<close> by (fact r1_eq)
thm r1_rec_def r1_rec_unfold r1_def r1_induct r2_r3_induct
end

text \<open>The global constants take the parameter as argument:\<close>
term \<open>L1.r1 :: int \<Rightarrow> int \<Rightarrow> int process\<close>

text \<open>Re-entering the locale:\<close>
context L1 begin
lemma \<open>r3 = k \<rightarrow> r2 k\<close> by (fact r3_eq)
end

text \<open>Interpretation:\<close>
interpretation L1_5 : L1 5 by standard simp
lemma \<open>L1_5.r1 x = x \<rightarrow> L1_5.r1 (x + 5)\<close> by (fact L1_5.r1_eq)

text \<open>Unnamed local contexts:\<close>
context fixes m :: int begin
Fixrec [RS] r4 :: \<open>int process\<close> where r4_eq : \<open>r4 = m \<rightarrow> r4\<close>
end
term \<open>r4 :: int \<Rightarrow> int process\<close>

text \<open>Polymorphic locales:\<close>
locale L3 = fixes e :: \<open>'a\<close>
begin
Fixrec [RS] r5 :: \<open>'a process\<close> where r5_eq : \<open>r5 = e \<rightarrow> r5\<close>
end

text \<open>In restriction spaces, \<open>\<sqinter> a \<in> A. _\<close> preserves constructiveness for arbitrary \<open>A\<close>:
no finiteness assumption is needed (in contrast to the HOLCF instance).\<close>
locale L2 = fixes A :: \<open>int set\<close>
begin
Fixrec [RS] r6 :: \<open>int process\<close> where r6_eq : \<open>r6 = (\<sqinter> a \<in> A. a \<rightarrow> r6)\<close>
end


chapter \<open>Tests Moved from the Instance Theory (verbatim)\<close>

section\<open>Test\<close>

Fixrec [RS] g :: \<open>'a \<Rightarrow> int process\<close> 
   and h :: \<open>'a \<Rightarrow> int process\<close>
   and j :: \<open>'a \<Rightarrow> int process\<close>
  where a : \<open>g = (\<lambda> x. \<box> a \<in> UNIV \<rightarrow> g x)\<close>
  |     b : \<open>h = (\<lambda> x. 4 \<rightarrow> j x)\<close>  
  |     c : \<open>j = (\<lambda> x. 5 \<rightarrow> h x)\<close>  

term g term h term j

(* generated stuff *)
thm g_h_j_rec_def g_h_j_rec_unfold g_def  h_def j_def a b c g_h_j_induct



lemma g_h_j_induct' :
  assumes * : \<open>adm\<^sub>\<down> ( \<lambda>(g::'a \<Rightarrow> int process, h::'a \<Rightarrow> int process, j::'a \<Rightarrow> int process). P' g h j)\<close>
    and   **: \<open>P' g\<^sub>0 h\<^sub>0 j\<^sub>0\<close>
    and  ***: "(\<And>g\<^sub>0 h\<^sub>0 j\<^sub>0. P' g\<^sub>0 h\<^sub>0 j\<^sub>0 \<Longrightarrow> P' (\<lambda>x. \<box> a \<in> UNIV \<rightarrow> g\<^sub>0 x) 
                                             (\<lambda> x. 4 \<rightarrow> j\<^sub>0 x)( \<lambda> x. 5 \<rightarrow> h\<^sub>0 x))"
  shows\<open>P' g h j\<close>

proof (rule def_restriction_fix_ind[OF g_h_j_rec_def, 
                                    where P = \<open>\<lambda>(g, h, j). P' g h j\<close> 
                                      and x = \<open>(g\<^sub>0,h\<^sub>0,j\<^sub>0)\<close>,simplified, simplified case_prod_beta,
                                    folded g_def h_def j_def, simplified] )
  show \<open>adm\<^sub>\<down> (\<lambda>(x, xa, y). P' x xa y)\<close> by fact
next
  show \<open>P' g\<^sub>0 h\<^sub>0 j\<^sub>0\<close> by fact
next
  from *** show \<open>P' (fst x) (fst (snd x)) (snd (snd x)) \<Longrightarrow>
                 P' (\<lambda>xa. \<box>a\<in>UNIV \<rightarrow> fst x xa) 
                    (\<lambda>xa. 4 \<rightarrow> snd (snd x) xa) 
                    (\<lambda>xa. 5 \<rightarrow> fst (snd x) xa)\<close> for x  by simp 
qed


section\<open>Simulation and Tests\<close>

ML\<open>
val t = @{term \<open>g\<^sub>0\<close>}

val s = "g"^"\<^sub>0"
\<close>


lemma aux : "s \<equiv> s' \<Longrightarrow> s' = t \<Longrightarrow> s = t" by auto
lemma aux2: "s = s' \<Longrightarrow> P s' = t \<Longrightarrow> P s = t" by auto

lemma a' : \<open>g = (\<lambda>x. \<box> a \<in> UNIV \<rightarrow> g x)\<close>
  thm g_def[THEN aux]
  apply (rule g_def[THEN aux])
  thm g_h_j_rec_unfold[THEN aux2]
  apply (rule g_h_j_rec_unfold[THEN aux2])
  apply (auto split: prod.split)
  by (metis g_def fst_conv snd_conv)

lemma a'' : \<open>g = (\<lambda>x. \<box> a \<in> UNIV \<rightarrow> g x)\<close>
 by(tactic \<open>RS_instance.prove_projection [@{thm g_def},@{thm h_def},@{thm j_def}] 
                              @{thm g_h_j_rec_unfold} 
                              @{context} 
                              @{thm g_def}\<close>)


lemma b'' : \<open>h = (\<lambda>x. (4 :: int) \<rightarrow> j x)\<close>
 by(tactic \<open>RS_instance.prove_projection [@{thm g_def},@{thm h_def},@{thm j_def}] 
                              @{thm g_h_j_rec_unfold} 
                              @{context} 
                              @{thm h_def}\<close>)

lemma c'' : \<open>j = (\<lambda> x. 5 \<rightarrow> h  x)\<close>
 by(tactic \<open>RS_instance.prove_projection [@{thm g_def},@{thm h_def},@{thm j_def}] 
                              @{thm g_h_j_rec_unfold} 
                              @{context} 
                              @{thm j_def}\<close>)



lemma restriction_fix_eq_defined : \<open>P = (\<upsilon> X. f X) \<Longrightarrow> constructive f \<Longrightarrow> P = f P\<close>
  using restriction_fix_eq by blast


definition g_h_j' :: \<open>('b \<Rightarrow> nat process) \<times> ('b \<Rightarrow> nat process) \<times> ('b \<Rightarrow> nat process)\<close>
  where \<open>g_h_j' \<equiv> \<upsilon> x. case x of 
                            (g', h', j') \<Rightarrow> (\<lambda>x. (3 :: nat) \<rightarrow> g' x, 
                                             \<lambda> x. (4 :: nat) \<rightarrow> j' x, \<lambda> x. 5 \<rightarrow> h' x)\<close>

definition g_h_j where \<open>g_h_j \<equiv> \<upsilon> (g, h, j). (\<lambda> x. \<box> a \<in> UNIV \<rightarrow> g x, 
                                              \<lambda> x. 4 \<rightarrow> j  x, 
                                              \<lambda> x. 5 \<rightarrow> h  x)\<close>

lemma g_h_j'_unfold : \<open>g_h_j' = (case g_h_j' of 
                                      (g', h', j') \<Rightarrow> (\<lambda> x. 3 \<rightarrow> g' x, 
                                                       \<lambda> x. 4 \<rightarrow> j' x, 
                                                       \<lambda> x. 5 \<rightarrow> h' x))\<close>
  apply (rule restriction_fix_eq_defined)
   apply (fact g_h_j'_def[THEN meta_eq_to_obj_eq])
  by auto

lemma [simp] : \<open>constructive f \<Longrightarrow> non_destructive (\<lambda>x. f (x, y))\<close>
  by (simp add: constructive_prod_domain_iff)

end
