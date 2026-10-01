(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSP - Seeing Processes as a Scott Space
 *
 * Author          : Benoît Ballenghien, Burkhart Wolff
 *
 * This file       : Conceptual tests of the HOLCF instance of Fixrec requiring HOL-CSPM 
 *
 * Copyright (c) 2025/26 Université Paris-Saclay, France
 ******************************************************************************\<close>
(*>*)

chapter \<open>The HOLCF Instance of \<^verbatim>\<open>Fixrec\<close> and the Operators of \<^session>\<open>HOL-CSPM\<close>\<close>

theory Fixrec_HOLCF_CSPM
  imports "HOL-CSP.Fixrec_HOLCF" "HOL-CSPM"
begin

text \<open>The tests of @{theory "HOL-CSP.Fixrec_HOLCF"} that involve operators of \<^session>\<open>HOL-CSPM\<close>.\<close>

text \<open>Recursion through the continuation of the exception operator \<open>\<Theta>\<close> (FDR's \<open>[| A |>\<close>),
also when the exception event is initial (as in the crash handling of Dali):\<close>
Fixrec cr :: \<open>int process\<close> and cr' :: \<open>int process\<close>
  where cr_eq  : \<open>cr  = ((1 \<rightarrow> Skip) ||| (0 \<rightarrow> Skip)) \<Theta> a \<in> {0}. cr'\<close>
  |     cr'_eq : \<open>cr' = ((2 \<rightarrow> Skip) ||| (0 \<rightarrow> Skip)) \<Theta> a \<in> {0}. cr'\<close>

end
