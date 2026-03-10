(***********************************************************************************
 * Copyright (c) 2025 Université Paris-Saclay
 *
 * Author: Benoît Ballenghien, Université Paris-Saclay,
 *         CNRS, ENS Paris-Saclay, LMF
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * * Redistributions of source code must retain the above copyright notice, this
 *
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 ***********************************************************************************)


chapter \<open>Declensions of the Generalized Synchronization Product\<close>

(*<*)
theory Synchronization_Product_Generalized_Interpretations
  imports Synchronization_Product_Generalized_Commutativity
    Synchronization_Product_Generalized_Associativity
    Read_Write_CSP_PTick_Laws
    Operational_Semantics_CSP_PTick_Laws
begin
  (*>*)

unbundle option_type_syntax


section \<open>Interpretations\<close>

text \<open>
For practical reasons, we directly interpret \<^locale>\<open>Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_locale\<close>.
Then, the laws of associativity will be derived
manually (instead of globally interpreting the locale \<^locale>\<open>Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_assoc_locale\<close>).
\<close>

subsection \<open>Classical Version\<close>

text (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) \<open>
The following interpretation is initially the reason we wanted the parameter
\<^term>\<open>tick_join\<close> to be of type \<^typ>\<open>'r \<Rightarrow> 's \<Rightarrow> 't option\<close> instead of
just \<^typ>\<open>'r \<Rightarrow> 's \<Rightarrow> 't\<close> (we wanted the operator \<^const>\<open>Sync\<close> already defined in
\<^session>\<open>HOL-CSP\<close> to indeed be a particular case of the new one).
\<close>

interpretation Sync\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c : Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_locale
  \<open>\<lambda>r s. if r = s then \<lfloor>r\<rfloor> else \<diamond>\<close>
  \<open>\<lambda>s r. if s = r then \<lfloor>s\<rfloor> else \<diamond>\<close> id id
  by unfold_locales (auto split: if_split_asm)

notation Sync\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k  (\<open>(_ \<lbrakk>_\<rbrakk>\<^sub>\<checkmark>\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c _)\<close> [70, 0, 71] 70)
notation Sync\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c.Inter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<open>(_ |||\<^sub>\<checkmark>\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c _)\<close> [72, 73] 72)
notation Sync\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c.Par\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k   (\<open>(_ ||\<^sub>\<checkmark>\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c _)\<close>  [74, 75] 74)



subsection \<open>Product Type\<close>

interpretation Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r : Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_locale
  \<open>\<lambda>r s. \<lfloor>(r, s)\<rfloor>\<close> \<open>\<lambda>s r. \<lfloor>(s, r)\<rfloor>\<close> prod.swap prod.swap
  by unfold_locales (auto split: if_split_asm)

notation Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k  (\<open>(_ \<lbrakk>_\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r _)\<close> [70, 0, 71] 70)
notation Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.Inter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<open>(_ |||\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r _)\<close> [72, 73] 72)
notation Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.Par\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k   (\<open>(_ ||\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r _)\<close>  [74, 75] 74)



subsection \<open>List Type\<close>

subsubsection \<open>Pair\<close>

interpretation Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t : Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_locale
  \<open>\<lambda>r s. \<lfloor>[r, s]\<rfloor>\<close> \<open>\<lambda>s r. \<lfloor>[s, r]\<rfloor>\<close>
  \<open>\<lambda>rs. [rs ! Suc 0, rs ! 0]\<close> \<open>\<lambda>rs. [rs ! Suc 0, rs ! 0]\<close>
  by unfold_locales (auto intro: inj_onI) 

notation Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k  (\<open>(_ \<lbrakk>_\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t _)\<close> [70, 0, 71] 70)
notation Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t.Inter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<open>(_ |||\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t _)\<close> [72, 73] 72)
notation Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t.Par\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k   (\<open>(_ ||\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t _)\<close>  [74, 75] 74)



subsubsection \<open>Right List\<close>

text \<open>
Here, we want to have one process of type \<^typ>\<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> on the left hand side,
and one of type \<^typ>\<open>('a, 'r list) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> on the right hand side.
\<close>

interpretation Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t : Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_locale
  \<open>\<lambda>r s. \<lfloor>r # s\<rfloor>\<close> \<open>\<lambda>s r. \<lfloor>s @ [r]\<rfloor>\<close>
  \<open>rotate1\<close> \<open>\<lambda>rs. if rs = [] then [] else last rs # butlast rs\<close>
  \<comment> \<open>\<^term>\<open>\<lambda>rs. last rs # butlast rs\<close> is not injective.\<close>
  by unfold_locales (auto intro: inj_onI) 

notation Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k  (\<open>(_ \<lbrakk>_\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t _)\<close> [70, 0, 71] 70)
notation Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.Inter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<open>(_ |||\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t _)\<close> [72, 73] 72)
notation Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.Par\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k   (\<open>(_ ||\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t _)\<close>  [74, 75] 74)



subsubsection \<open>Left List\<close>

text \<open>
Here, we want to have one process of type \<^typ>\<open>('a, 'r list) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
on the left hand side, and one of type \<^typ>\<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> on the right hand side.
There is no need to do a new interpretation, the operator we are looking for is actually
the symmetric of the one we defined just above.
\<close>

notation Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_locale_sym.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k  (\<open>(_ \<lbrakk>_\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t _)\<close> [70, 0, 71] 70)
notation Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_locale_sym.Inter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<open>(_ |||\<^sub>\<checkmark>\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t _)\<close> [72, 73] 72)
notation Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_locale_sym.Par\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k   (\<open>(_ ||\<^sub>\<checkmark>\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t _)\<close>  [74, 75] 74)



subsubsection \<open>Arbitrary Lists\<close>

text \<open>
We believed for a long time that it was not possible to handle the case
where both processes have their ticks of type \<^typ>\<open>'r list\<close>.
Indeed the concatenation on the lists is not injective, resulting in
the impossibility of interpreting \<^locale>\<open>Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale\<close>.
But it turns out that by adding some control on the length of the lists,
we actually can!
\<close>

paragraph \<open>Control on one side\<close>

context fixes lenL :: nat begin

global_interpretation Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L : Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_locale 
  \<open>\<lambda>r s. if length r = lenL then \<lfloor>r @ s\<rfloor> else \<diamond>\<close>
  \<open>\<lambda>s r. if length r = lenL then \<lfloor>s @ r\<rfloor> else \<diamond>\<close>
  \<open>\<lambda>rs. drop lenL rs @ take lenL rs\<close>
  \<open>\<lambda>rs. rev (take lenL (rev rs)) @ rev (drop lenL (rev rs))\<close>
  by unfold_locales (auto split: if_split_asm)

end

abbreviation Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_syntax ::
  \<open>[('a, 'r list) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, nat, 'a set, ('a, 'r list) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k]
   \<Rightarrow> ('a, 'r list) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> (\<open>(_ \<^bsub>_\<^esub>(\<lbrakk>_\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L) _)\<close> [70, 0, 0, 71] 70)
  where \<open>P \<^bsub>lenL\<^esub>\<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L Q \<equiv> Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k lenL P A Q\<close>

abbreviation Inter\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_syntax ::
  \<open>[('a, 'r list) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, nat, ('a, 'r list) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k]
   \<Rightarrow> ('a, 'r list) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> (\<open>(_ \<^bsub>_\<^esub>(|||\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L) _)\<close> [72, 0, 73] 72)
  where \<open>P \<^bsub>lenL\<^esub>|||\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L Q \<equiv> Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L.Inter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k lenL P Q\<close>

abbreviation Par\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_syntax ::
  \<open>[('a, 'r list) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, nat, ('a, 'r list) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k]
   \<Rightarrow> ('a, 'r list) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> (\<open>(_ \<^bsub>_\<^esub>(||\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L) _)\<close> [74, 0, 75] 75)
  where \<open>P \<^bsub>lenL\<^esub>||\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L Q \<equiv> Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L.Par\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k lenL P Q\<close>


text \<open>
The control is done on the left process, so with the symmetric version
of this operator we control the ticks length of the right one.
\<close>

abbreviation Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>R_syntax ::
  \<open>[('a, 'r list) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, nat, 'a set, ('a, 'r list) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k]
   \<Rightarrow> ('a, 'r list) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> (\<open>(_ \<^bsub>_\<^esub>(\<lbrakk>_\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>R) _)\<close> [70, 0, 0, 71] 70)
  where \<open>P \<^bsub>lenL\<^esub>\<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>R Q \<equiv> Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_locale_sym.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k lenL P A Q\<close>

abbreviation Inter\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>R_syntax ::
  \<open>[('a, 'r list) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, nat, ('a, 'r list) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k]
   \<Rightarrow> ('a, 'r list) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> (\<open>(_ \<^bsub>_\<^esub>(|||\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>R) _)\<close> [72, 0, 73] 72)
  where \<open>P \<^bsub>lenL\<^esub>|||\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>R Q \<equiv> Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_locale_sym.Inter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k lenL P Q\<close>

abbreviation Par\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>R_syntax ::
  \<open>[('a, 'r list) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, nat, ('a, 'r list) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k]
   \<Rightarrow> ('a, 'r list) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> (\<open>(_ \<^bsub>_\<^esub>(||\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>R) _)\<close> [74, 0, 75] 75)
  where \<open>P \<^bsub>lenL\<^esub>||\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>R Q \<equiv> Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym.Par\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k lenL P Q\<close>



paragraph \<open>Control on both sides\<close>

context fixes lenL :: nat and lenR :: nat begin

global_interpretation Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s : Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_locale 
  \<open>\<lambda>r s. if length r = lenL \<and> length s = lenR then \<lfloor>r @ s\<rfloor> else \<diamond>\<close>
  \<open>\<lambda>s r. if length s = lenR \<and> length r = lenL then \<lfloor>s @ r\<rfloor> else \<diamond>\<close>
  \<open>\<lambda>rs. drop lenL rs @ take lenL rs\<close>
  \<open>\<lambda>rs. drop lenR rs @ take lenR rs\<close>
  by unfold_locales (auto split: if_split_asm)

end


abbreviation Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s_syntax ::
  \<open>[('a, 'r list) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, nat, 'a set, nat, ('a, 'r list) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k]
   \<Rightarrow> ('a, 'r list) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> (\<open>(_ \<^bsub>_\<^esub>(\<lbrakk>_\<rbrakk>\<^sub>\<checkmark>)\<^bsub>_\<^esub> _)\<close> [70, 0, 0, 0, 71] 70)
  where \<open>P \<^bsub>lenL\<^esub>\<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^bsub>lenR\<^esub> Q \<equiv> Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k lenL lenR P A Q\<close>

abbreviation Inter\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s_syntax ::
  \<open>[('a, 'r list) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, nat, nat, ('a, 'r list) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k]
   \<Rightarrow> ('a, 'r list) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> (\<open>(_ \<^bsub>_\<^esub>(|||\<^sub>\<checkmark>)\<^bsub>_\<^esub> _)\<close> [72, 0, 0, 73] 72)
  where \<open>P \<^bsub>lenL\<^esub>|||\<^sub>\<checkmark>\<^bsub>lenR\<^esub> Q \<equiv> Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s.Inter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k lenL lenR P Q\<close>

abbreviation Par\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s_syntax ::
  \<open>[('a, 'r list) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, nat, nat, ('a, 'r list) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k]
   \<Rightarrow> ('a, 'r list) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> (\<open>(_ \<^bsub>_\<^esub>(||\<^sub>\<checkmark>)\<^bsub>_\<^esub> _)\<close> [74, 0, 0, 75] 75)
  where \<open>P \<^bsub>lenL\<^esub>||\<^sub>\<checkmark>\<^bsub>lenR\<^esub> Q \<equiv> Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s.Par\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k lenL lenR P Q\<close>



section \<open>Associativities\<close>

subsection \<open>Classical Version\<close>

lemma Sync\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c_assoc :
  \<open>P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c (Q \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c R) = P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c Q \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c R\<close>
proof -
  let ?f = \<open>\<lambda>r s. if r = s then \<lfloor>r\<rfloor> else \<diamond>\<close>
  interpret * : Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_assoc_locale ?f ?f ?f ?f id id
    by (unfold_locales) (auto split: if_split_asm)
  show ?thesis by (fact "*.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_assoc"[simplified Renaming_id])
qed



subsection \<open>Product Type\<close>

lemma Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_assoc :
  \<open>P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r (Q \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r R) = RenamingTick (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r Q \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r R) (\<lambda>((r, s), t). (r, s, t))\<close>
proof -
  interpret * : Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_assoc_locale \<open>\<lambda>r s. \<lfloor>(r, s)\<rfloor>\<close> \<open>\<lambda>r s. \<lfloor>(r, s)\<rfloor>\<close> \<open>\<lambda>r s. \<lfloor>(r, s)\<rfloor>\<close>
    \<open>\<lambda>r s. \<lfloor>(r, s)\<rfloor>\<close> \<open>\<lambda>((r, s), t). (r, s, t)\<close> \<open>\<lambda>(r, s, t). ((r, s), t)\<close>
    by unfold_locales auto
  show ?thesis by (fact "*.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_assoc")
qed



subsection \<open>List Type\<close>

lemma Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_assoc :
  \<open>P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t (Q \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t R) = (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t Q) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t R\<close>
proof -
  interpret * : Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_assoc_locale \<open>\<lambda>r s. \<lfloor>[r, s]\<rfloor>\<close> \<open>\<lambda>r s. \<lfloor>r @ [s]\<rfloor>\<close>
    \<open>\<lambda>r s. \<lfloor>r # s\<rfloor>\<close> \<open>\<lambda>r s. \<lfloor>[r, s]\<rfloor>\<close> id id
    by unfold_locales auto
  show ?thesis by (fact "*.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_assoc"[unfolded Renaming_id])
qed


lemma Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t_assoc :
  \<open>P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t (Q \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t R) = (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t Q) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t R\<close>
proof -
  interpret * : Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_assoc_locale \<open>\<lambda>r s. \<lfloor>r # s\<rfloor>\<close> \<open>\<lambda>r s. \<lfloor>r @ [s]\<rfloor>\<close>
    \<open>\<lambda>r s. \<lfloor>r # s\<rfloor>\<close> \<open>\<lambda>r s. \<lfloor>r @ [s]\<rfloor>\<close> id id
    by unfold_locales auto
  show ?thesis by (fact "*.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_assoc"[unfolded Renaming_id])
qed


lemma Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_assoc :
  \<open>P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t (Q \<^bsub>lenQ\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L R) = (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t Q) \<^bsub>Suc lenQ\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L R\<close>
proof -
  interpret * : Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_assoc_locale
    \<open>\<lambda>r s. \<lfloor>r # s\<rfloor>\<close>
    \<open>\<lambda>r s. if length r = Suc lenQ then \<lfloor>r @ s\<rfloor> else \<diamond>\<close>
    \<open>\<lambda>r s. \<lfloor>r # s\<rfloor>\<close>
    \<open>\<lambda>r s. if length r = lenQ then \<lfloor>r @ s\<rfloor> else \<diamond>\<close> id id
    by unfold_locales (auto split: if_split_asm)
  show ?thesis by (fact "*.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_assoc"[unfolded Renaming_id])
qed

lemma Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>R_Sync\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t_assoc :
  \<open>P \<^bsub>Suc lenQ\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>R (Q \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t R) = (P \<^bsub>lenQ\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>R Q) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t R\<close>
proof -
  interpret * : Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_assoc_locale
    \<open>\<lambda>r s. if length s = lenQ then \<lfloor>r @ s\<rfloor> else \<diamond>\<close>
    \<open>\<lambda>r s. \<lfloor>r @ [s]\<rfloor>\<close>
    \<open>\<lambda>r s. if length s = Suc lenQ then \<lfloor>r @ s\<rfloor> else \<diamond>\<close>
    \<open>\<lambda>r s. \<lfloor>r @ [s]\<rfloor>\<close> id id
    by unfold_locales (auto split: if_split_asm)
  show ?thesis by (fact "*.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_assoc"[unfolded Renaming_id])
qed


lemma Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s_assoc :
  \<open>P \<^bsub>lenP\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^bsub>lenQ + lenR\<^esub> (Q \<^bsub>lenQ\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^bsub>lenR\<^esub> R) =
   P \<^bsub>lenP\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^bsub>lenQ\<^esub> Q \<^bsub>lenP + lenQ\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^bsub>lenR\<^esub> R\<close>
proof -
  interpret * : Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_assoc_locale
    \<open>\<lambda>r s. if length r = lenP \<and> length s = lenQ then \<lfloor>r @ s\<rfloor> else \<diamond>\<close>
    \<open>\<lambda>r s. if length r = lenP + lenQ \<and> length s = lenR then \<lfloor>r @ s\<rfloor> else \<diamond>\<close>
    \<open>\<lambda>r s. if length r = lenP \<and> length s = lenQ + lenR then \<lfloor>r @ s\<rfloor> else \<diamond>\<close>
    \<open>\<lambda>r s. if length r = lenQ \<and> length s = lenR then \<lfloor>r @ s\<rfloor> else \<diamond>\<close> id id
    by unfold_locales (auto split: if_split_asm)
  show ?thesis by (fact "*.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_assoc"[unfolded Renaming_id])
qed


lemma Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_assoc :
  \<open>P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t (Q \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t R) = (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t Q) \<^bsub>Suc (Suc 0)\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L R\<close>
proof -
  interpret * : Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_assoc_locale
    \<open>\<lambda>r s. \<lfloor>[r, s]\<rfloor>\<close>
    \<open>\<lambda>r s. if length r = Suc (Suc 0) then \<lfloor>r @ s\<rfloor> else \<diamond>\<close>
    \<open>\<lambda>r s. \<lfloor>r # s\<rfloor>\<close>
    \<open>\<lambda>r s. \<lfloor>r # s\<rfloor>\<close> id id
    by unfold_locales (auto split: if_split_asm)
  show ?thesis by (fact "*.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_assoc"[unfolded Renaming_id])
qed

lemma Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>R_Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_assoc :
  \<open>P \<^bsub>Suc (Suc 0)\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>R (Q \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t R) = (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t Q) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t R\<close>
proof -
  interpret * : Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_assoc_locale
    \<open>\<lambda>r s. \<lfloor>r @ [s]\<rfloor>\<close>
    \<open>\<lambda>r s. \<lfloor>r @ [s]\<rfloor>\<close>
    \<open>\<lambda>r s. if length s = Suc (Suc 0) then \<lfloor>r @ s\<rfloor> else \<diamond>\<close>
    \<open>\<lambda>r s. \<lfloor>[r, s]\<rfloor>\<close> id id
    by unfold_locales (auto split: if_split_asm)
  show ?thesis by (fact "*.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_assoc"[unfolded Renaming_id])
qed



section \<open>Properties\<close>

subsection \<open>Actual Generalization\<close>

text \<open>
We can actually recover the classical synchronization product defined in
session \<^session>\<open>HOL-CSP\<close> as a particular case of our generalization.
\<close>

theorem Sync\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c_is_Sync : \<open>P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c Q = P \<lbrakk>A\<rbrakk> Q\<close>
proof (rule Process_eq_optimizedI)
  show \<open>t \<in> \<D> (P \<lbrakk>A\<rbrakk> Q) \<Longrightarrow> t \<in> \<D> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c Q)\<close> for t
    by (simp add: D_Sync Sync\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c.D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k'
        flip: setinterleaves_is_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
      (metis setinterleaving_sym)
next
  show \<open>t \<in> \<D> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c Q) \<Longrightarrow> t \<in> \<D> (P \<lbrakk>A\<rbrakk> Q)\<close> for t
    by (simp add: D_Sync Sync\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c.D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
        flip: setinterleaves_is_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
      (metis setinterleaving_sym)
next
  fix t X assume \<open>(t, X) \<in> \<F> (P \<lbrakk>A\<rbrakk> Q)\<close> \<open>t \<notin> \<D> (P \<lbrakk>A\<rbrakk> Q)\<close>
  then obtain t_P t_Q X_P X_Q
    where * : \<open>(t_P, X_P) \<in> \<F> P\<close> \<open>(t_Q, X_Q) \<in> \<F> Q\<close>
      \<open>t setinterleaves ((t_P, t_Q), range tick \<union> ev ` A)\<close>
      \<open>X = (X_P \<union> X_Q) \<inter> (range tick \<union> ev ` A) \<union> X_P \<inter> X_Q\<close>
    unfolding Sync_projs by blast
  from "*"(4) have \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<lambda>r s. if r = s then \<lfloor>r\<rfloor> else \<diamond>) X_P A X_Q\<close>
    by (auto simp add: super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def subset_iff)
      (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust)
  with "*"(1-3) show \<open>(t, X) \<in> \<F> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c Q)\<close>
    by (auto simp add: Sync\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c.F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k setinterleaves_is_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
next
  fix t X assume \<open>(t, X) \<in> \<F> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c Q)\<close> \<open>t \<notin> \<D> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c Q)\<close>
  then obtain t_P t_Q X_P X_Q
    where * : \<open>(t_P, X_P) \<in> \<F> P\<close> \<open>(t_Q, X_Q) \<in> \<F> Q\<close>
      \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>\<lambda>r s. if r = s then \<lfloor>r\<rfloor> else \<diamond>\<^esub> ((t_P, t_Q), A)\<close>
      \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<lambda>r s. if r = s then \<lfloor>r\<rfloor> else \<diamond>) X_P A X_Q\<close>
    unfolding Sync\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
  from "*"(1-3) have \<open>(t, (X_P \<union> X_Q) \<inter> (range tick \<union> ev ` A) \<union> X_P \<inter> X_Q) \<in> \<F> (P \<lbrakk>A\<rbrakk> Q)\<close>
    by (simp add: F_Sync setinterleaves_is_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) blast
  moreover from "*"(4) have \<open>X \<subseteq> (X_P \<union> X_Q) \<inter> (range tick \<union> ev ` A) \<union> X_P \<inter> X_Q\<close>
    by (auto simp add: super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def subset_iff split: if_split_asm)
  ultimately show \<open>(t, X) \<in> \<F> (P \<lbrakk>A\<rbrakk> Q)\<close> by (meson is_processT4)
qed



subsection \<open>Other Properties\<close>

lemma \<open>Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k lenL lenR Q A P = P \<^bsub>lenL\<^esub>\<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^bsub>lenR\<^esub> Q\<close>
  by (simp add: Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_sym)


corollary TickSwap_Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r [simp] : \<open>TickSwap (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r Q) = Q \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P\<close>
  by (simp add: Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_commute TickSwap_is_Renaming)

lemma TickSwap_is_Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_iff [simp] :
  \<open>TickSwap P = Q \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r R \<longleftrightarrow> P = R \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r Q\<close>
  by (simp add: TickSwap_eq_iff_eq_TickSwap)

corollary Sync\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c_commute : \<open>P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c Q = Q \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c P\<close>
  by (fact Sync\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_commute[simplified])


lemma \<open>RenamingTick (P \<^bsub>lenL\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^bsub>lenR\<^esub> Q) (\<lambda>r_s. drop lenL r_s @ take lenL r_s) =
       Q \<^bsub>lenR\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^bsub>lenL\<^esub> P\<close>
  by (fact Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_commute)



section \<open>Ticks Length and Conversions\<close>

text \<open>
Through \<^const>\<open>RenamingTick\<close>, conversions can be established between the interpretations.
For this, we sometimes need an assumption about the length of the ticks.
\<close>

subsection \<open>Ticks Length\<close>

subsubsection \<open>Definition and first Properties\<close>

definition is_ticks_length ::
  \<open>nat \<Rightarrow> ('a, 'r list) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> bool\<close> (\<open>(length\<^sub>\<checkmark>)\<^bsub>_\<^esub>('(_'))\<close>)
  where \<open>length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P) \<equiv> \<forall>rs \<in> \<^bold>\<checkmark>\<^bold>s(P). length rs = n\<close>

text \<open>
We might imagine \<^term>\<open> \<forall>rs \<in> \<checkmark>s(P). length rs = n\<close> instead.
But when the process \<^term>\<open>P\<close> has divergences, the predicate would not hold.
Additionally, we only need the control about traces that are not divergences.
\<close>

lemma is_ticks_lengthI : \<open>(\<And>rs. rs \<in> \<^bold>\<checkmark>\<^bold>s(P) \<Longrightarrow> length rs = n) \<Longrightarrow> length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P)\<close>
  by (simp add: is_ticks_length_def)

lemma is_ticks_lengthD : \<open>length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P) \<Longrightarrow> rs \<in> \<^bold>\<checkmark>\<^bold>s(P) \<Longrightarrow> length rs = n\<close>
  by (simp add: is_ticks_length_def)


lemma is_ticks_length_unique :
  \<comment>\<open>Not suitable for simplifier.\<close>
  \<open>length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P) \<longleftrightarrow> \<^bold>\<checkmark>\<^bold>s(P) = {} \<or> (\<forall>m. length\<^sub>\<checkmark>\<^bsub>m\<^esub>(P) \<longleftrightarrow> m = n)\<close>
  by (auto simp add: is_ticks_length_def)

lemma empty_strict_ticks_of_imp_is_ticks_length :
  \<open>\<^bold>\<checkmark>\<^bold>s(P) = {} \<Longrightarrow> length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P)\<close>
  using is_ticks_length_unique by blast

lemma nonempty_strict_ticks_of_imp_is_ticks_length_unique :
  \<open>\<^bold>\<checkmark>\<^bold>s(P) \<noteq> {} \<Longrightarrow> length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P) \<Longrightarrow> length\<^sub>\<checkmark>\<^bsub>m\<^esub>(P) \<Longrightarrow> m = n\<close> 
  using is_ticks_length_unique by blast



subsubsection \<open>Behaviour\<close>

named_theorems is_ticks_length_simp
named_theorems is_ticks_length_intro

paragraph \<open>Constant Processes\<close>

lemma is_ticks_length_STOP [is_ticks_length_simp] :
  \<open>length\<^sub>\<checkmark>\<^bsub>n\<^esub>(STOP)\<close> by (simp add: empty_strict_ticks_of_imp_is_ticks_length)

lemma is_ticks_length_BOT [is_ticks_length_simp] :
  \<open>length\<^sub>\<checkmark>\<^bsub>n\<^esub>(\<bottom>)\<close> by (simp add: empty_strict_ticks_of_imp_is_ticks_length)

lemma is_ticks_length_SKIP_iff [is_ticks_length_simp] :
  \<open>length\<^sub>\<checkmark>\<^bsub>n\<^esub>(SKIP rs) \<longleftrightarrow> length rs = n\<close>
  by (simp add: is_ticks_length_def)

lemma is_ticks_length_SKIPS_iff [is_ticks_length_simp] :
  \<open>length\<^sub>\<checkmark>\<^bsub>n\<^esub>(SKIPS R) \<longleftrightarrow> (\<forall>rs \<in> R. length rs = n)\<close>
  by (simp add: is_ticks_length_def strict_ticks_of_def SKIPS_projs)



paragraph \<open>Binary (or less) Operators\<close>

lemma is_ticks_length_Ndet [is_ticks_length_intro] :
  \<open>length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P) \<Longrightarrow> length\<^sub>\<checkmark>\<^bsub>n\<^esub>(Q) \<Longrightarrow> length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P \<sqinter> Q)\<close>
  by (simp add: is_ticks_length_def)
    (meson Un_iff strict_ticks_of_Ndet_subset subset_iff)

lemma is_ticks_length_Det [is_ticks_length_intro] :
  \<open>length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P) \<Longrightarrow> length\<^sub>\<checkmark>\<^bsub>n\<^esub>(Q) \<Longrightarrow> length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P \<box> Q)\<close>
  by (simp add: is_ticks_length_def)
    (meson Un_iff strict_ticks_of_Det_subset subset_iff)

lemma is_ticks_length_Sliding [is_ticks_length_intro] :
  \<open>length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P) \<Longrightarrow> length\<^sub>\<checkmark>\<^bsub>n\<^esub>(Q) \<Longrightarrow> length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P \<rhd> Q)\<close>
  by (simp add: is_ticks_length_def)                
    (meson Un_iff strict_ticks_of_Sliding_subset subset_iff)


lemma is_ticks_length_Sync [is_ticks_length_intro] :
  \<open>length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P) \<Longrightarrow> length\<^sub>\<checkmark>\<^bsub>n\<^esub>(Q) \<Longrightarrow> length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P \<lbrakk>S\<rbrakk> Q)\<close>
  by (simp add: is_ticks_length_def)
    (meson Int_iff strict_ticks_of_Sync_subset subset_iff)


lemma is_ticks_length_Seq [is_ticks_length_intro] :
  \<open>non_terminating P \<or> length\<^sub>\<checkmark>\<^bsub>n\<^esub>(Q) \<Longrightarrow> length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P \<^bold>; Q)\<close>
proof (elim disjE)
  show \<open>non_terminating P \<Longrightarrow> length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P \<^bold>; Q)\<close>
    by (metis is_ticks_length_def non_terminating_Seq non_terminating_is_right
        non_tickFree_tick strict_ticks_of_memE tickFree_append_iff)
next
  from strict_ticks_of_Seq_subset[of P Q]
  show \<open>length\<^sub>\<checkmark>\<^bsub>n\<^esub>(Q) \<Longrightarrow> length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P \<^bold>; Q)\<close>
    by (auto simp add: is_ticks_length_def split: if_split_asm)
qed


lemma is_ticks_length_Hiding [is_ticks_length_intro] :
  \<open>length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P \ S)\<close> if \<open>length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P)\<close>
proof (rule is_ticks_lengthI)
  fix rs assume \<open>rs \<in> \<^bold>\<checkmark>\<^bold>s(P \ S)\<close>
  then obtain t t' where \<open>t = t' @ [\<checkmark>(rs)]\<close> \<open>t \<in> \<T> (P \ S)\<close> \<open>t \<notin> \<D> (P \ S)\<close>
    by (metis is_processT9 strict_ticks_of_memE)
  from this(2, 3) obtain u where \<open>t = trace_hide u (ev ` S)\<close> \<open>u \<in> \<T> P\<close>
    unfolding T_Hiding D_Hiding using F_T by fast
  from this(1) this(2)[THEN T_imp_front_tickFree] obtain u' where \<open>u = u' @ [\<checkmark>(rs)]\<close>
    by (cases u rule: rev_cases, simp_all add: \<open>t = t' @ [\<checkmark>(rs)]\<close> split: if_split_asm)
      (metis Hiding_tickFree front_tickFree_nonempty_append_imp list.distinct(1)
        non_tickFree_tick tickFree_append_iff)
  from \<open>t \<notin> \<D> (P \ S)\<close> mem_D_imp_mem_D_Hiding[of u P S]
  have \<open>u \<notin> \<D> P\<close> unfolding \<open>t = trace_hide u (ev ` S)\<close> by blast
  with \<open>u \<in> \<T> P\<close> \<open>u = u' @ [\<checkmark>(rs)]\<close> have \<open>rs \<in> \<^bold>\<checkmark>\<^bold>s(P)\<close>
    by (simp add: strict_ticks_of_memI)
  with that show \<open>length rs = n\<close> by (simp add: is_ticks_lengthD)
qed


lemma is_ticks_length_Interrupt [is_ticks_length_intro] :
  \<open>length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P) \<Longrightarrow> length\<^sub>\<checkmark>\<^bsub>n\<^esub>(Q) \<Longrightarrow> length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P \<triangle> Q)\<close>
  by (simp add: is_ticks_length_def)
    (meson Un_iff strict_ticks_of_Interrupt_subset subsetD)


\<comment> \<open>Missing lemma from \<^session>\<open>HOL-CSPM\<close>\<close>
lemma strict_ticks_Throw_subset :
  \<open>\<^bold>\<checkmark>\<^bold>s(P \<Theta> a\<in>A. Q a) \<subseteq> \<^bold>\<checkmark>\<^bold>s(P) \<union> (\<Union>a\<in>A \<inter> \<alpha>(P). \<^bold>\<checkmark>\<^bold>s(Q a))\<close>
proof (rule subsetI)
  fix r assume \<open>r \<in> \<^bold>\<checkmark>\<^bold>s(P \<Theta> a\<in>A. Q a)\<close>
  then obtain t where \<open>t @ [\<checkmark>(r)] \<in> \<T> (P \<Theta> a\<in>A. Q a)\<close> \<open>t @ [\<checkmark>(r)] \<notin> \<D> (P \<Theta> a\<in>A. Q a)\<close>
    by (meson is_processT9 strict_ticks_of_memE)
  then consider \<open>t @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>t @ [\<checkmark>(r)] \<notin> \<D> P\<close>
    | t1 a t2 where \<open>t @ [\<checkmark>(r)] = t1 @ ev a # t2\<close> \<open>t1 @ [ev a] \<in> \<T> P\<close>
      \<open>a \<in> A\<close> \<open>t2 \<in> \<T> (Q a)\<close> \<open>t2 \<notin> \<D> (Q a)\<close>
    by (simp add: Throw_projs)
      (metis (no_types, lifting) append_T_imp_tickFree
        front_tickFree_single is_processT9 not_Cons_self2)
  thus \<open>r \<in> \<^bold>\<checkmark>\<^bold>s(P) \<union> (\<Union>a\<in>A \<inter> \<alpha>(P). \<^bold>\<checkmark>\<^bold>s(Q a))\<close>
  proof cases
    show \<open>t @ [\<checkmark>(r)] \<in> \<T> P \<Longrightarrow> t @ [\<checkmark>(r)] \<notin> \<D> P \<Longrightarrow> r \<in> \<^bold>\<checkmark>\<^bold>s(P) \<union> (\<Union>a\<in>A \<inter> \<alpha>(P). \<^bold>\<checkmark>\<^bold>s(Q a))\<close>
      by (simp add: strict_ticks_of_memI)
  next
    show \<open>\<lbrakk>t @ [\<checkmark>(r)] = t1 @ ev a # t2; t1 @ [ev a] \<in> \<T> P; a \<in> A; t2 \<in> \<T> (Q a); t2 \<notin> \<D> (Q a)\<rbrakk>
           \<Longrightarrow> r \<in> \<^bold>\<checkmark>\<^bold>s(P) \<union> (\<Union>a\<in>A \<inter> \<alpha>(P). \<^bold>\<checkmark>\<^bold>s(Q a))\<close> for t1 a t2
      by (cases t2 rule: rev_cases, simp_all)
        (meson IntI events_of_memI in_set_conv_decomp strict_ticks_of_memI)
  qed
qed

lemma is_ticks_length_Throw [is_ticks_length_intro] :
  \<open>length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P \<Theta> a \<in> A. Q a)\<close>
  if \<open>length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P)\<close> \<open>\<And>a. a \<in> \<alpha>(P) \<Longrightarrow> length\<^sub>\<checkmark>\<^bsub>n\<^esub>(Q a)\<close>
proof -
  from that have \<open>\<forall>rs\<in>\<^bold>\<checkmark>\<^bold>s(P) \<union> (\<Union>a\<in>A \<inter> \<alpha>(P). \<^bold>\<checkmark>\<^bold>s(Q a)). length rs = n\<close>
    by (auto simp add: is_ticks_length_def)
  with strict_ticks_Throw_subset show \<open>length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P \<Theta> a \<in> A. Q a)\<close>
    unfolding is_ticks_length_def by fast
qed

lemma is_ticks_length_Renaming [is_ticks_length_intro] :
  \<open>length\<^sub>\<checkmark>\<^bsub>n\<^esub>(Renaming P f g) \<close> if \<open>\<And>r. r \<in> \<^bold>\<checkmark>\<^bold>s(P) \<Longrightarrow> length (g r) = n\<close>
proof (rule is_ticks_lengthI)
  fix rs assume \<open>rs \<in> \<^bold>\<checkmark>\<^bold>s(Renaming P f g)\<close>
  then obtain t where \<open>t @ [\<checkmark>(rs)] \<in> \<T> (Renaming P f g)\<close>
    \<open>t @ [\<checkmark>(rs)] \<notin> \<D> (Renaming P f g)\<close>
    by (meson is_processT9 strict_ticks_of_memE)
  then obtain u where * : \<open>t @ [\<checkmark>(rs)] = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u\<close> and \<open>u \<in> \<T> P\<close>
    by (auto simp add: Renaming_projs)
  from this(1) \<open>u \<in> \<T> P\<close> append_T_imp_tickFree obtain u' r
    where \<open>rs = g r\<close> \<open>u = u' @ [\<checkmark>(r)]\<close> \<open>tF u'\<close>
    by (cases u rule: rev_cases) (auto simp add: tick_eq_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)
  from "*" \<open>t @ [\<checkmark>(rs)] \<notin> \<D> (Renaming P f g)\<close> this(2, 3) front_tickFree_Cons_iff
  have \<open>u' \<notin> \<D> P\<close> by (auto simp add: D_Renaming)
  moreover from \<open>u \<in> \<T> P\<close> have \<open>u' @ [\<checkmark>(r)] \<in> \<T> P\<close>
    by (simp add: \<open>u = u' @ [\<checkmark>(r)]\<close>)
  ultimately have \<open>r \<in> \<^bold>\<checkmark>\<^bold>s(P)\<close> by (meson is_processT9 strict_ticks_of_memI)
  with that have \<open>length (g r) = n\<close> by blast
  thus \<open>length rs = n\<close> by (simp add: \<open>rs = g r\<close>)
qed



paragraph \<open>Architectural Operators\<close>

lemma is_ticks_length_GlobalNdet [is_ticks_length_intro] :
  \<open>(\<And>a. a \<in> A \<Longrightarrow> length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P a)) \<Longrightarrow> length\<^sub>\<checkmark>\<^bsub>n\<^esub>(\<sqinter>a \<in> A. P a)\<close>
  by (simp add: is_ticks_length_def)
    (metis (no_types, lifting) UN_E strict_ticks_of_GlobalNdet_subset subsetD)

lemma is_ticks_length_GlobalDet [is_ticks_length_intro] :
  \<open>(\<And>a. a \<in> A \<Longrightarrow> length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P a)) \<Longrightarrow> length\<^sub>\<checkmark>\<^bsub>n\<^esub>(\<box>a \<in> A. P a)\<close>
  by (simp add: is_ticks_length_def)
    (metis (no_types, lifting) UN_E strict_ticks_of_GlobalDet_subset subsetD)

lemma is_ticks_length_MultiSync [is_ticks_length_intro] :
  \<open>(\<And>m. m \<in> set_mset M \<Longrightarrow> length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P m)) \<Longrightarrow> length\<^sub>\<checkmark>\<^bsub>n\<^esub>(\<^bold>\<lbrakk>S\<^bold>\<rbrakk> m \<in># M. P m)\<close>
  by (induct M rule: induct_subset_mset_empty_single)
    (simp_all add: is_ticks_length_STOP is_ticks_length_Sync)

lemma is_ticks_length_MultiSeq [is_ticks_length_intro] :
  \<open>L \<noteq> [] \<Longrightarrow> length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P (last L)) \<Longrightarrow> length\<^sub>\<checkmark>\<^bsub>n\<^esub>(SEQ l \<in>@ L. P l)\<close>
  by (induct L rule: rev_induct)
    (simp_all add: is_ticks_length_Seq)


paragraph \<open>Communications\<close>

lemma is_ticks_length_write0_iff [is_ticks_length_simp] :
  \<open>length\<^sub>\<checkmark>\<^bsub>n\<^esub>(e \<rightarrow> P) \<longleftrightarrow> length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P)\<close>
  by (simp add: is_ticks_length_def strict_ticks_of_write0)

lemma is_ticks_length_write_iff [is_ticks_length_simp] :
  \<open>length\<^sub>\<checkmark>\<^bsub>n\<^esub>(c\<^bold>!e \<rightarrow> P) \<longleftrightarrow> length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P)\<close>
  by (simp add: is_ticks_length_def strict_ticks_of_write)

lemma is_ticks_length_Mprefix_iff [is_ticks_length_simp] :
  \<open>length\<^sub>\<checkmark>\<^bsub>n\<^esub>(\<box>a \<in> A \<rightarrow> P a) = (\<forall>a \<in> A. length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P a))\<close> 
  by (auto simp add: is_ticks_length_def strict_ticks_of_Mprefix)

lemma is_ticks_length_read_iff [is_ticks_length_simp] :
  \<open>length\<^sub>\<checkmark>\<^bsub>n\<^esub>(c\<^bold>?a\<in>A \<rightarrow> P a) = (\<forall>b \<in> c ` A. length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P (inv_into A c b)))\<close>
  by (simp add: read_def is_ticks_length_Mprefix_iff)

corollary \<open>inj_on c A \<Longrightarrow> length\<^sub>\<checkmark>\<^bsub>n\<^esub>(c\<^bold>?a\<in>A \<rightarrow> P a) = (\<forall>a \<in> A. length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P a))\<close>
  by (simp add: is_ticks_length_read_iff)

lemma is_ticks_length_Mndetprefix_iff [is_ticks_length_simp] :
  \<open>length\<^sub>\<checkmark>\<^bsub>n\<^esub>(\<sqinter>a \<in> A \<rightarrow> P a) = (\<forall>a \<in> A. length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P a))\<close> 
  by (auto simp add: is_ticks_length_def strict_ticks_of_Mndetprefix)

lemma is_ticks_length_ndet_write_iff [is_ticks_length_simp] :
  \<open>length\<^sub>\<checkmark>\<^bsub>n\<^esub>(c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a) = (\<forall>b \<in> c ` A. length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P (inv_into A c b)))\<close>
  by (simp add: ndet_write_def is_ticks_length_Mndetprefix_iff)

corollary \<open>inj_on c A \<Longrightarrow> length\<^sub>\<checkmark>\<^bsub>n\<^esub>(c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a) = (\<forall>a \<in> A. length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P a))\<close>
  by (simp add: is_ticks_length_ndet_write_iff)



paragraph \<open>Generalizations\<close>

lemma strict_ticks_of_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset : \<open>\<^bold>\<checkmark>\<^bold>s(P \<^bold>;\<^sub>\<checkmark> Q) \<subseteq> \<Union> {\<^bold>\<checkmark>\<^bold>s(Q r) |r. r \<in> \<^bold>\<checkmark>\<^bold>s(P)}\<close>
  by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs append_eq_map_conv elim!: strict_ticks_of_memE)
    (metis tickFree_Nil non_tickFree_tick tickFree_map_ev_comp
           front_tickFree_charn tickFree_append_iff tickFree_append_iff
           last_snoc[of \<open>map (ev \<circ> of_ev) _ @ _\<close>] last_snoc[of _ \<open>\<checkmark>(_)\<close>]
           butlast_snoc[of \<open>map (ev \<circ> of_ev) _ @ _\<close>] butlast_snoc[of _ \<open>\<checkmark>(_)\<close>]
           append.assoc[of \<open>map (ev \<circ> of_ev) _\<close> _ \<open>[_]\<close>] tickFree_imp_front_tickFree
           T_imp_front_tickFree is_processT9 strict_ticks_of_memI,
      metis butlast_append butlast_snoc front_tickFree_iff_tickFree_butlast non_tickFree_tick
            tickFree_append_iff tickFree_imp_front_tickFree tickFree_map_ev_comp)


lemma non_terminating_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>P \<^bold>;\<^sub>\<checkmark> Q = RenamingTick P g\<close> if \<open>non_terminating P\<close>
proof -
  from \<open>non_terminating P\<close> have \<pounds> : \<open>\<D> P = {}\<close> \<open>t @ [\<checkmark>(r)] \<notin> \<T> P\<close> for t r
    by (force simp add: non_terminating_is_right nonterminating_implies_div_free)+
  show \<open>P \<^bold>;\<^sub>\<checkmark> Q = RenamingTick P g\<close>
  proof (rule Process_eq_optimizedI)
    show \<open>t \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> Q) \<Longrightarrow> t \<in> \<D> (RenamingTick P g)\<close>
      and \<open>t \<in> \<D> (RenamingTick P g) \<Longrightarrow> t \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> Q)\<close> for t
      by (simp_all add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs Renaming_projs "\<pounds>")
  next
    fix t X assume \<open>(t, X) \<in> \<F> (P \<^bold>;\<^sub>\<checkmark> Q)\<close>
    then obtain t' where * : \<open>t = map (ev \<circ> of_ev) t'\<close>
      \<open>(t', ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X) \<in> \<F> P\<close> \<open>tF t'\<close>
      by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs Renaming_projs "\<pounds>")
    have $ : \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id g) t'\<close>
      by (simp add: "*"(1, 3) tickFree_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is)
    have $$ : \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id g -` X \<subseteq> ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X\<close>
      by (simp add: subset_iff ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def image_iff)
        (metis Int_iff event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.sel(1) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.simps(9) id_apply rangeI)
    show \<open>(t, X) \<in> \<F> (RenamingTick P g)\<close>
      by (simp add: Renaming_projs) (metis "$" "$$" "*"(2) is_processT4)
  next
    fix t X assume \<open>(t, X) \<in> \<F> (RenamingTick P g)\<close>
    then obtain t' where * : \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id g) t'\<close>
      \<open>(t', map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id g -` X) \<in> \<F> P\<close>
      by (auto simp add: Renaming_projs "\<pounds>")
    from "*"(2) F_T non_terminating_is_right \<open>non_terminating P\<close> have \<open>tF t'\<close> by blast
    have \<open>(t', map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id g -` X \<union> range tick) \<in> \<F> P\<close>
      by (rule is_processT5[OF "*"(2)]) (use "\<pounds>"(2) F_T in blast)
    moreover have \<open>ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X \<subseteq> map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id g -` X \<union> range tick\<close>
      by (auto simp add: ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
    ultimately have \<open>(t', ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X) \<in> \<F> P\<close>
      by (metis is_processT4)
    moreover have \<open>t = map (ev \<circ> of_ev) t'\<close>
      by (simp add: "*"(1) \<open>tF t'\<close> tickFree_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is)
    ultimately show \<open>(t, X) \<in> \<F> (P \<^bold>;\<^sub>\<checkmark> Q)\<close>
      by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs \<open>tF t'\<close>)
  qed
qed



lemma is_ticks_length_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k [is_ticks_length_intro] :
  \<open>non_terminating P \<or> (\<forall>r\<in>\<^bold>\<checkmark>\<^bold>s(P). length\<^sub>\<checkmark>\<^bsub>n\<^esub>(Q r)) \<Longrightarrow> length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P \<^bold>;\<^sub>\<checkmark> Q)\<close>
proof (elim disjE)
  assume \<open>non_terminating P\<close>
  hence \<open>\<^bold>\<checkmark>\<^bold>s(P) = {}\<close>
    by (metis (full_types) non_terminating_Seq strict_ticks_of_BOT
                           strict_ticks_of_Seq_subset subset_empty)
  show \<open>non_terminating P \<Longrightarrow> length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P \<^bold>;\<^sub>\<checkmark> Q)\<close>
    by (subst non_terminating_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, assumption)
      (rule is_ticks_length_Renaming, simp add: is_ticks_length_Renaming \<open>\<^bold>\<checkmark>\<^bold>s(P) = {}\<close>)
next
  from strict_ticks_of_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset[of P Q]
  show \<open>\<forall>r\<in>\<^bold>\<checkmark>\<^bold>s(P). length\<^sub>\<checkmark>\<^bsub>n\<^esub>(Q r) \<Longrightarrow> length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P \<^bold>;\<^sub>\<checkmark> Q)\<close>
    by (auto simp add: is_ticks_length_def)
qed



lemma is_ticks_length_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>length\<^sub>\<checkmark>\<^bsub>n\<^esub>(Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k tick_join P A Q)\<close>
  \<comment> \<open>We cannot work directly inside the locale since in this context
      the types of ticks \<^typ>\<open>'t\<close> cannot be set to \<^typ>\<open>'r list\<close>.\<close>
  if \<open>Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale tick_join\<close>
    and \<open>\<And>r s. r \<in> \<^bold>\<checkmark>\<^bold>s(P) \<Longrightarrow> s \<in> \<^bold>\<checkmark>\<^bold>s(Q) \<Longrightarrow>
       case tick_join r s of \<diamond> \<Rightarrow> True | \<lfloor>r_s\<rfloor> \<Rightarrow> length r_s = n\<close>
proof -
  interpret Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale tick_join
    by (fact \<open>Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale tick_join\<close>)
  show \<open>length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q)\<close>
  proof (rule is_ticks_lengthI)
    fix rs assume \<open>rs \<in> \<^bold>\<checkmark>\<^bold>s(P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q)\<close>
    then obtain t where \<open>t @ [\<checkmark>(rs)] \<in> \<T> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q)\<close> \<open>t @ [\<checkmark>(rs)] \<notin> \<D> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q)\<close>
      by (meson is_processT9 strict_ticks_of_memE)
    then obtain t_P t_Q where \<open>t_P \<in> \<T> P\<close> \<open>t_Q \<in> \<T> Q\<close>
      and "*" : \<open>t @ [\<checkmark>(rs)] setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, t_Q), A)\<close>
      unfolding Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
    with \<open>t @ [\<checkmark>(rs)] \<notin> \<D> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q)\<close> have \<open>t_P \<notin> \<D> P\<close> \<open>t_Q \<notin> \<D> Q\<close>
      by (simp add: D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k', use front_tickFree_Nil in blast)+
    from "*" obtain r s t_P' t_Q'
      where \<open>tick_join r s = \<lfloor>rs\<rfloor>\<close> \<open>t_P = t_P' @ [\<checkmark>(r)]\<close> \<open>t_Q = t_Q' @ [\<checkmark>(s)]\<close>
      by (blast elim: snoc_tick_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
    from this(2, 3) \<open>t_P \<notin> \<D> P\<close> \<open>t_Q \<notin> \<D> Q\<close> \<open>t_P \<in> \<T> P\<close> \<open>t_Q \<in> \<T> Q\<close>
    have \<open>r \<in> \<^bold>\<checkmark>\<^bold>s(P)\<close> \<open>s \<in> \<^bold>\<checkmark>\<^bold>s(Q)\<close> by (metis strict_ticks_of_memI)+
    from that(2)[OF this, unfolded \<open>tick_join r s = \<lfloor>rs\<rfloor>\<close>] show \<open>length rs = n\<close> by simp 
  qed
qed



lemma is_ticks_length_One_RenamingTick_singl [is_ticks_length_simp] :
  \<open>length\<^sub>\<checkmark>\<^bsub>Suc 0\<^esub>(RenamingTick P (\<lambda>r. [r]))\<close>
  by (simp add: is_ticks_length_Renaming)

lemma is_ticks_length_Two_Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t [is_ticks_length_simp] :
  \<open>length\<^sub>\<checkmark>\<^bsub>Suc (Suc 0)\<^esub>(P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t Q)\<close>
  by (simp add: is_ticks_length_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[OF Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_axioms])


lemma is_ticks_length_Suc_Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t [is_ticks_length_intro] :
  \<open>length\<^sub>\<checkmark>\<^bsub>n\<^esub>(Q) \<Longrightarrow> length\<^sub>\<checkmark>\<^bsub>Suc n\<^esub>(P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t Q)\<close>
  by (rule is_ticks_length_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[OF Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_axioms])
    (simp add: is_ticks_lengthD)

text \<open>The equivalence is false.\<close>

lemma False if \<open>\<And>P Q n. length\<^sub>\<checkmark>\<^bsub>Suc n\<^esub>(P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t Q) \<Longrightarrow> length\<^sub>\<checkmark>\<^bsub>n\<^esub>(Q)\<close>
  using that[of 0 STOP \<open>SKIP [undefined]\<close>]
  by (simp add: is_ticks_length_STOP is_ticks_length_SKIP_iff)


lemma is_ticks_length_Suc_Sync\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t [is_ticks_length_intro] :
  \<open>length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P) \<Longrightarrow> length\<^sub>\<checkmark>\<^bsub>Suc n\<^esub>(P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t Q)\<close>
  by (rule is_ticks_length_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
      [OF Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_locale_sym.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_axioms])
    (simp add: is_ticks_lengthD)

lemma is_ticks_length_sum_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L [is_ticks_length_intro] :
  \<open>length\<^sub>\<checkmark>\<^bsub>m\<^esub>(Q) \<Longrightarrow> length\<^sub>\<checkmark>\<^bsub>n + m\<^esub>(P \<^bsub>n\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L Q)\<close>
  by (rule is_ticks_length_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[OF Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_axioms])
    (simp add: is_ticks_lengthD)

lemma is_ticks_length_sum_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>R [is_ticks_length_intro] :
  \<open>length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P) \<Longrightarrow> length\<^sub>\<checkmark>\<^bsub>n + m\<^esub>(P \<^bsub>m\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>R Q)\<close>
  by (rule is_ticks_length_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
      [OF Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_locale_sym.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_axioms])
    (simp add: is_ticks_lengthD)

lemma is_ticks_length_sum_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s [is_ticks_length_intro] :
  \<open>length\<^sub>\<checkmark>\<^bsub>n + m\<^esub>(P \<^bsub>n\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^bsub>m\<^esub> Q)\<close>
  by (rule is_ticks_length_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[OF Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_axioms]) simp



subsection \<open>Conversions\<close>

lemma Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_to_Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t :
  \<open>P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t Q = P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t RenamingTick Q (\<lambda>s. [s])\<close>
  by (rule Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.inj_RenamingTick_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_inj_RenamingTick
      [of id \<open>\<lambda>s. [s]\<close>, simplified, symmetric])
    (auto intro: inj_onI)

lemma Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_to_Sync\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t :
  \<open>P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t Q = RenamingTick P (\<lambda>r. [r]) \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t Q\<close>
  by (rule Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_locale_sym.inj_RenamingTick_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_inj_RenamingTick
      [of \<open>\<lambda>r. [r]\<close> id, simplified, symmetric])
    (auto intro: inj_onI)


lemma Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_to_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L :
  \<open>P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t Q = RenamingTick P (\<lambda>r. [r]) \<^bsub>Suc 0\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L Q\<close>
  by (rule Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L.inj_RenamingTick_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_inj_RenamingTick
      [of \<open>\<lambda>r. [r]\<close> id \<open>Suc 0\<close>, simplified, symmetric])
    (auto intro: inj_onI)

lemma Sync\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t_to_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>R :
  \<open>P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t Q = P \<^bsub>Suc 0\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>R RenamingTick Q (\<lambda>s. [s])\<close>
  by (rule Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_locale_sym.inj_RenamingTick_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_inj_RenamingTick
      [of id \<open>\<lambda>s. [s]\<close> \<open>Suc 0\<close>, simplified, symmetric])
    (auto intro: inj_onI)


lemma Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_to_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s :
  \<open>length\<^sub>\<checkmark>\<^bsub>m\<^esub>(Q) \<Longrightarrow> P \<^bsub>n\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L Q = P \<^bsub>n\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^bsub>m\<^esub> Q\<close>
  by (auto intro!: Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_same_tick_join_on_strict_ticks_of
      Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_axioms
      dest: is_ticks_lengthD)

lemma Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>R_to_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s :
  \<open>length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P) \<Longrightarrow> P \<^bsub>m\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>R Q = P \<^bsub>n\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^bsub>m\<^esub> Q\<close>
  by (auto intro!: Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_same_tick_join_on_strict_ticks_of
      Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_locale_sym.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_axioms
      dest: is_ticks_lengthD)

corollary Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_is_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>R :
  \<open>length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P) \<Longrightarrow> length\<^sub>\<checkmark>\<^bsub>m\<^esub>(Q) \<Longrightarrow> P \<^bsub>n\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L Q = P \<^bsub>m\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>R Q\<close>
  by (simp add: Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_to_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>R_to_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s)


corollary Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_to_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L :
  \<open>P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t Q = RenamingTick P (\<lambda>r. [r]) \<^bsub>Suc 0\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L RenamingTick Q (\<lambda>s. [s])\<close>
  by (simp add: Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_to_Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_to_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L)

corollary Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_to_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>R :
  \<open>P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t Q = RenamingTick P (\<lambda>r. [r]) \<^bsub>Suc 0\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>R RenamingTick Q (\<lambda>s. [s])\<close>
  by (simp add: Sync\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t_to_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>R Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_to_Sync\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t)

corollary Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_to_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s :
  \<open>length\<^sub>\<checkmark>\<^bsub>m\<^esub>(Q) \<Longrightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t Q = RenamingTick P (\<lambda>r. [r]) \<^bsub>Suc 0\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^bsub>m\<^esub> Q\<close>
  by (simp add: Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_to_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_to_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L)

corollary Sync\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t_to_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s :
  \<open>length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P) \<Longrightarrow> P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t Q = P \<^bsub>n\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^bsub>Suc 0\<^esub> RenamingTick Q (\<lambda>s. [s])\<close>
  by (simp add: Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>R_to_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s Sync\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t_to_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>R)

corollary Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_to_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s :
  \<open>P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t Q = RenamingTick P (\<lambda>r. [r]) \<^bsub>Suc 0\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^bsub>Suc 0\<^esub> RenamingTick Q (\<lambda>s. [s])\<close>
  by (simp add: Sync\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t_to_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_to_Sync\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t
      is_ticks_length_One_RenamingTick_singl)




lemma Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_to_Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t :
  \<open>RenamingTick (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r Q) (\<lambda>(r, s). [r, s]) = P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t Q\<close>
  by (rule Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.inj_on_RenamingTick_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
      [of \<open>\<lambda>(r, s). [r, s]\<close>, simplified])
    (auto intro: inj_onI)

lemma Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_to_Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r :
  \<open>RenamingTick (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t Q) (\<lambda>rs. (rs ! 0, rs ! Suc 0)) = P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r Q\<close>
  by (rule Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t.inj_on_RenamingTick_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
      [of \<open>\<lambda>rs. (rs ! 0, rs ! Suc 0)\<close>, simplified])
    (auto intro: inj_onI)

lemma Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_to_Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t :
  \<open>RenamingTick (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r Q) (\<lambda>(r, s). r # s) = P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t Q\<close>
  by (rule Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.inj_on_RenamingTick_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
      [of \<open>\<lambda>(r, s). r # s\<close>, simplified])
    (auto intro: inj_onI)

lemma Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_to_Sync\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t :
  \<open>RenamingTick (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r Q) (\<lambda>(r, s). r @ [s]) = P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t Q\<close>
  by (rule Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.inj_on_RenamingTick_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
      [of \<open>\<lambda>(r, s). r @ [s]\<close>, simplified])
    (auto intro: inj_onI)


lemma Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_to_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L :
  \<open>RenamingTick (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r Q) (\<lambda>(r, s). r @ s) = P \<^bsub>n\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L Q\<close>
  (is \<open>?lhs = ?rhs\<close>) if \<open>length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P)\<close>
proof -
  let ?g = \<open>\<lambda>rs. (take n rs, drop n rs)\<close>
  let ?g' = \<open>\<lambda>(r, s). r @ s\<close>
  let ?RT = RenamingTick
  have \<open>?RT ?lhs ?g = ?RT ?rhs ?g\<close>
  proof (subst Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L.inj_on_RenamingTick_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
    show \<open>inj_on ?g (Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L.range_tick_join n)\<close>
      by (rule inj_onI) (auto split: if_split_asm)
  next
    have \<open>?RT (?RT (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r Q) ?g') ?g = P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r Q\<close>
    proof (fold RenamingTick_comp, subst (2) RenamingTick_id[of \<open>P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r Q\<close>, symmetric])
      show \<open>?RT (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r Q) (?g \<circ> ?g') = ?RT (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r Q) id\<close>
      proof (rule RenamingTick_is_restrictable_on_strict_ticks_of)
        from that show \<open>rs \<in> \<^bold>\<checkmark>\<^bold>s(P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r Q) \<Longrightarrow> (?g \<circ> (\<lambda>(x, y). x @ y)) rs = id rs\<close> for rs
          by (auto dest!: set_mp[OF Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.strict_ticks_of_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset] is_ticks_lengthD)
      qed
    qed
    also have \<open>P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r Q =
               Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
               (\<lambda>r s. case if length r = n then \<lfloor>r @ s\<rfloor> else \<diamond>
                      of \<diamond> \<Rightarrow> \<diamond> | \<lfloor>rs\<rfloor> \<Rightarrow> \<lfloor>?g rs\<rfloor>) P S Q\<close> (is \<open>_ = ?rhs'\<close>)
      by (rule Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_same_tick_join_on_strict_ticks_of[symmetric], unfold_locales)
        (use \<open>length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P)\<close> in \<open>auto split: if_split_asm dest: is_ticks_lengthD\<close>)
    finally show \<open>?RT ?lhs ?g = ?rhs'\<close> .
  qed
  hence \<open>?RT (?RT ?lhs ?g) ?g' = ?RT (?RT ?rhs ?g) ?g'\<close> by simp
  also from \<open>length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P)\<close> have \<open>?RT (?RT ?lhs ?g) ?g' = ?lhs\<close>
    by (auto simp flip: RenamingTick_comp intro!: RenamingTick_is_restrictable_on_strict_ticks_of
                 dest!: set_mp[OF Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.strict_ticks_of_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset] is_ticks_lengthD)
  also from \<open>length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P)\<close> have \<open>?RT (?RT ?rhs ?g) ?g' = ?rhs\<close>
    by (fold RenamingTick_comp, subst (2) RenamingTick_id[of ?rhs, symmetric])
      (auto simp del: RenamingTick_id intro!: RenamingTick_is_restrictable_on_strict_ticks_of
               dest!: set_mp[OF Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.strict_ticks_of_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset] is_ticks_lengthD)
  finally show \<open>?lhs = ?rhs\<close> .
qed


corollary Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_to_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>R :
  \<open>RenamingTick (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r Q) (\<lambda>(r, s). r @ s) = P \<^bsub>n\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>R Q\<close>
  (is \<open>?lhs = ?rhs\<close>) if \<open>length\<^sub>\<checkmark>\<^bsub>n\<^esub>(Q)\<close>
proof -
  let ?RT = RenamingTick
  have \<open>?RT (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r Q) (\<lambda>(x, y). x @ y) =
        ?RT (Q \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P) ((\<lambda>(x, y). x @ y) \<circ> prod.swap)\<close>
    by (simp add: RenamingTick_comp subst Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_commute)
  also from \<open>length\<^sub>\<checkmark>\<^bsub>n\<^esub>(Q)\<close>
  have \<open>\<dots> = ?RT (Q \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P) ((\<lambda>rs. drop n rs @ take n rs) \<circ> (\<lambda>(x, y). x @ y))\<close>
    by (auto intro!: RenamingTick_is_restrictable_on_strict_ticks_of
              dest!: set_mp[OF Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.strict_ticks_of_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset] is_ticks_lengthD)
  also have \<open>\<dots> = ?RT (Q \<^bsub>n\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L P) (\<lambda>rs. drop n rs @ take n rs)\<close>
    by (simp add: RenamingTick_comp Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_to_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L[OF \<open>length\<^sub>\<checkmark>\<^bsub>n\<^esub>(Q)\<close>])
  also have \<open>\<dots> = P \<^bsub>n\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>R Q\<close>
    by (fact Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_commute)
  finally show \<open>?lhs = ?rhs\<close> .
qed

corollary Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_to_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s :
  \<open>RenamingTick (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r Q) (\<lambda>(r, s). r @ s) = P \<^bsub>n\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^bsub>m\<^esub> Q\<close>
  (is \<open>?lhs = ?rhs\<close>) if \<open>length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P)\<close> and \<open>length\<^sub>\<checkmark>\<^bsub>m\<^esub>(Q)\<close>
  by (subst Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_to_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L[OF \<open>length\<^sub>\<checkmark>\<^bsub>n\<^esub>(P)\<close>])
    (rule Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_to_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s[OF \<open>length\<^sub>\<checkmark>\<^bsub>m\<^esub>(Q)\<close>])



section \<open>First Laws\<close>

corollary Inter\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c_STOP [simp] :
  \<open>P |||\<^sub>\<checkmark>\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c STOP = P \<^bold>; STOP\<close>
  by (simp add: Sync\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c.Inter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_STOP[of P id])

corollary Inter\<^sub>P\<^sub>a\<^sub>i\<^sub>r_STOP :
  \<open>P |||\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r STOP = RenamingTick (P \<^bold>; STOP) (\<lambda>r. (r, g r))\<close>
  by (simp add: Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.Inter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_STOP[of P g])

corollary Inter\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_STOP :
  \<open>P |||\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t STOP = RenamingTick (P \<^bold>; STOP) (\<lambda>r. [r, g r])\<close>
  by (simp add: Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t.Inter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_STOP[of P g])

corollary Inter\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_STOP :
  \<open>P |||\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t STOP = RenamingTick (P \<^bold>; STOP) (\<lambda>r. r # g r)\<close>
  by (simp add: Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.Inter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_STOP[of P g])

corollary Inter\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t_STOP :
  \<open>P |||\<^sub>\<checkmark>\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t STOP = RenamingTick (P \<^bold>; STOP) (\<lambda>r. r @ [g r])\<close>
  by (simp add: Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_locale_sym.Inter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_STOP[of P g])

corollary Inter\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_STOP :
  \<open>P \<^bsub>n\<^esub>|||\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L STOP =
   RenamingTick (P \<^bold>; STOP) (\<lambda>r. if length r = n then r @ g r else undefined)\<close>
  by (auto simp add: Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L.Inter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_STOP[of n P g] option.the_def
      intro!: arg_cong[where f = \<open>RenamingTick (P \<^bold>; STOP)\<close>])

corollary Inter\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>R_STOP :
  \<open>P \<^bsub>n\<^esub>|||\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>R STOP =
   RenamingTick (P \<^bold>; STOP) (\<lambda>r. if length (g r) = n then r @ g r else undefined)\<close>
  by (auto simp add: Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_locale_sym.Inter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_STOP[of n P g] option.the_def
      intro!: arg_cong[where f = \<open>RenamingTick (P \<^bold>; STOP)\<close>])

corollary Inter\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s_STOP :
  \<open>P \<^bsub>n\<^esub>|||\<^sub>\<checkmark>\<^bsub>m\<^esub> STOP =
   RenamingTick (P \<^bold>; STOP) (\<lambda>r. if length r = n \<and> length (g r) = m then r @ g r else undefined)\<close>
  by (auto simp add: Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s.Inter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_STOP[of n m P g] option.the_def
      intro!: arg_cong[where f = \<open>RenamingTick (P \<^bold>; STOP)\<close>])



corollary STOP_Inter\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c [simp] :
  \<open>STOP |||\<^sub>\<checkmark>\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c Q = Q \<^bold>; STOP\<close>
  by (simp add: Sync\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c.STOP_Inter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[of Q id])

corollary STOP_Inter\<^sub>P\<^sub>a\<^sub>i\<^sub>r :
  \<open>STOP |||\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r Q = RenamingTick (Q \<^bold>; STOP) (\<lambda>s. (g s, s))\<close>
  by (simp add: Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.STOP_Inter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[of Q g])

corollary STOP_Inter\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t :
  \<open>STOP |||\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t Q = RenamingTick (Q \<^bold>; STOP) (\<lambda>s. [g s, s])\<close>
  by (simp add: Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t.STOP_Inter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[of Q g])

corollary STOP_Inter\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t :
  \<open>STOP |||\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t Q = RenamingTick (Q \<^bold>; STOP) (\<lambda>s. g s # s)\<close>
  by (simp add: Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.STOP_Inter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[of Q g])

corollary STOP_Inter\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t :
  \<open>STOP |||\<^sub>\<checkmark>\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t Q = RenamingTick (Q \<^bold>; STOP) (\<lambda>s. g s @ [s])\<close>
  by (simp add: Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_locale_sym.STOP_Inter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[of Q g])

corollary STOP_Inter\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L :
  \<open>STOP \<^bsub>n\<^esub>|||\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L Q =
   RenamingTick (Q \<^bold>; STOP) (\<lambda>r. if length (g r) = n then g r @ r else undefined)\<close>
  by (auto simp add: Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L.STOP_Inter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[of n Q g] option.the_def
      intro!: arg_cong[where f = \<open>RenamingTick (Q \<^bold>; STOP)\<close>])

corollary STOP_Inter\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>R :
  \<open>STOP \<^bsub>n\<^esub>|||\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>R Q =
   RenamingTick (Q \<^bold>; STOP) (\<lambda>r. if length r = n then g r @ r else undefined)\<close>
  by (auto simp add: Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_locale_sym.STOP_Inter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[of n Q g] option.the_def
      intro!: arg_cong[where f = \<open>RenamingTick (Q \<^bold>; STOP)\<close>])

corollary STOP_Inter\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s :
  \<open>STOP \<^bsub>n\<^esub>|||\<^sub>\<checkmark>\<^bsub>m\<^esub> Q =
   RenamingTick (Q \<^bold>; STOP) (\<lambda>r. if length (g r) = n \<and> length r = m then g r @ r else undefined)\<close>
  by (auto simp add: Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s.STOP_Inter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[of n m Q g] option.the_def
      intro!: arg_cong[where f = \<open>RenamingTick (Q \<^bold>; STOP)\<close>])



corollary SKIP_Sync\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c_SKIP :
  \<open>SKIP r \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c SKIP s =
   (if r = s then SKIP r else STOP)\<close> by simp

corollary SKIP_Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_SKIP :
  \<open>SKIP r \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r SKIP s = SKIP (r, s)\<close> by simp

corollary SKIP_Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_SKIP :
  \<open>SKIP r \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t SKIP s = SKIP [r, s]\<close> by simp

corollary SKIP_Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_SKIP :
  \<open>SKIP r \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t SKIP s = SKIP (r # s)\<close> by simp

corollary SKIP_Sync\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t_SKIP :
  \<open>SKIP r \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t SKIP s = SKIP (r @ [s])\<close> by simp

corollary SKIP_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_SKIP :
  \<open>SKIP r \<^bsub>n\<^esub>\<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L SKIP s =
   (if length r = n then SKIP (r @ s) else STOP)\<close> by simp

corollary SKIP_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>R_SKIP :
  \<open>SKIP r \<^bsub>n\<^esub>\<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>R SKIP s =
   (if length s = n then SKIP (r @ s) else STOP)\<close> by simp

corollary SKIP_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s_SKIP :
  \<open>SKIP r \<^bsub>n\<^esub>\<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^bsub>m\<^esub> SKIP s =
   (if length r = n \<and> length s = m then SKIP (r @ s) else STOP)\<close> by simp





section \<open>Operational Laws\<close>

subsection \<open>Classical Version\<close>

locale After_Sync\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c_locale = After_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale \<open>\<lambda>r s. if r = s then \<lfloor>r\<rfloor> else \<diamond>\<close>
begin

\<comment> \<open>Just checking...\<close>
lemma \<open>Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k P S Q = P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c Q\<close> by (fact refl)

end

locale AfterExt_Sync\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c_locale =
  AfterExt_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale \<open>\<lambda>r s. if r = s then \<lfloor>r\<rfloor> else \<diamond>\<close>

sublocale AfterExt_Sync\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c_locale \<subseteq> After_Sync\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c_locale
  by unfold_locales

locale OpSemTransitions_Sync\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c_locale =
  OpSemTransitions_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale \<open>\<lambda>r s. if r = s then \<lfloor>r\<rfloor> else \<diamond>\<close>

sublocale OpSemTransitions_Sync\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c_locale \<subseteq> AfterExt_Sync\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c_locale
  by unfold_locales


subsection \<open>Product Type\<close>

locale After_Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_locale = After_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale \<open>\<lambda>r s. \<lfloor>(r, s)\<rfloor>\<close>
begin

\<comment> \<open>Just checking...\<close>
lemma \<open>Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k P S Q = P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r Q\<close> by (fact refl)

end

locale AfterExt_Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_locale =
  AfterExt_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale \<open>\<lambda>r s. \<lfloor>(r, s)\<rfloor>\<close>

sublocale AfterExt_Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_locale \<subseteq> After_Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_locale
  by unfold_locales

locale OpSemTransitions_Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_locale =
  OpSemTransitions_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale \<open>\<lambda>r s. \<lfloor>(r, s)\<rfloor>\<close>

sublocale OpSemTransitions_Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_locale \<subseteq> AfterExt_Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_locale
  by unfold_locales



subsection \<open>List Type\<close>

subsubsection \<open>Pair\<close>

locale After_Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_locale = After_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale \<open>\<lambda>r s. \<lfloor>[r, s]\<rfloor>\<close>
begin

\<comment> \<open>Just checking...\<close>
lemma \<open>Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k P S Q = P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t Q\<close> by (fact refl)

end

locale AfterExt_Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_locale =
  AfterExt_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale \<open>\<lambda>r s. \<lfloor>[r, s]\<rfloor>\<close>

sublocale AfterExt_Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_locale \<subseteq> After_Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_locale
  by unfold_locales

locale OpSemTransitions_Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_locale =
  OpSemTransitions_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale \<open>\<lambda>r s. \<lfloor>[r, s]\<rfloor>\<close>

sublocale OpSemTransitions_Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_locale \<subseteq> AfterExt_Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_locale
  by unfold_locales



subsubsection \<open>Right List\<close>

locale After_Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_locale = After_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale \<open>\<lambda>r s. \<lfloor>r # s\<rfloor>\<close>
begin

\<comment> \<open>Just checking...\<close>
lemma \<open>Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k P S Q = P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t Q\<close> by (fact refl)

end

locale AfterExt_Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_locale =
  AfterExt_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale \<open>\<lambda>r s. \<lfloor>r # s\<rfloor>\<close>

sublocale AfterExt_Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_locale \<subseteq> After_Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_locale
  by unfold_locales

locale OpSemTransitions_Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_locale =
  OpSemTransitions_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale \<open>\<lambda>r s. \<lfloor>r # s\<rfloor>\<close>

sublocale OpSemTransitions_Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_locale \<subseteq> AfterExt_Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_locale
  by unfold_locales



subsubsection \<open>Left List\<close>

locale After_Sync\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t_locale = After_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale \<open>\<lambda>r s. \<lfloor>r @ [s]\<rfloor>\<close>
begin

\<comment> \<open>Just checking...\<close>
lemma \<open>Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k P S Q = P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t Q\<close> by (fact refl)

end

locale AfterExt_Sync\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t_locale =
  AfterExt_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale \<open>\<lambda>r s. \<lfloor>r @ [s]\<rfloor>\<close>

sublocale AfterExt_Sync\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t_locale \<subseteq> After_Sync\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t_locale
  by unfold_locales

locale OpSemTransitions_Sync\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t_locale =
  OpSemTransitions_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale \<open>\<lambda>r s. \<lfloor>r @ [s]\<rfloor>\<close>

sublocale OpSemTransitions_Sync\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t_locale \<subseteq> AfterExt_Sync\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t_locale
  by unfold_locales



subsubsection \<open>Arbitrary Lists\<close>

paragraph \<open>Control on left side\<close>

locale After_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_locale =
  After_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale \<open>\<lambda>r s. if length r = lenL then \<lfloor>r @ s\<rfloor> else \<diamond>\<close>
  for lenL :: nat
begin

\<comment> \<open>Just checking...\<close>
lemma \<open>Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k P S Q = P \<^bsub>lenL\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L Q\<close> by (fact refl)

end

locale AfterExt_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_locale =
  AfterExt_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale \<open>\<lambda>r s. if length r = lenL then \<lfloor>r @ s\<rfloor> else \<diamond>\<close>
  for lenL :: nat

sublocale AfterExt_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_locale \<subseteq> After_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_locale
  by unfold_locales

locale OpSemTransitions_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_locale =
  OpSemTransitions_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale \<open>\<lambda>r s. if length r = lenL then \<lfloor>r @ s\<rfloor> else \<diamond>\<close>
  for lenL :: nat

sublocale OpSemTransitions_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_locale \<subseteq> AfterExt_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_locale
  by unfold_locales



paragraph \<open>Control on right side\<close>

locale After_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>R_locale =
  After_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale \<open>\<lambda>r s. if length s = lenR then \<lfloor>r @ s\<rfloor> else \<diamond>\<close>
  for lenR :: nat
begin

\<comment> \<open>Just checking...\<close>
lemma \<open>Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k P S Q = P \<^bsub>lenR\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>R Q\<close> by (fact refl)

end

locale AfterExt_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>R_locale =
  AfterExt_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale \<open>\<lambda>r s. if length s = lenR then \<lfloor>r @ s\<rfloor> else \<diamond>\<close>
  for lenR :: nat

sublocale AfterExt_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>R_locale \<subseteq> After_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>R_locale
  by unfold_locales

locale OpSemTransitions_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>R_locale =
  OpSemTransitions_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale \<open>\<lambda>r s. if length r = lenL then \<lfloor>r @ s\<rfloor> else \<diamond>\<close>
  for lenL :: nat

sublocale OpSemTransitions_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>R_locale \<subseteq> AfterExt_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>R_locale
  by unfold_locales



paragraph \<open>Control on both sides\<close>

locale After_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s_locale =
  After_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale
  \<open>\<lambda>r s. if length r = lenL \<and> length s = lenR then \<lfloor>r @ s\<rfloor> else \<diamond>\<close>
  for lenL lenR :: nat
begin

\<comment> \<open>Just checking...\<close>
lemma \<open>Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k P S Q = P \<^bsub>lenL\<^esub>\<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^bsub>lenR\<^esub> Q\<close> by (fact refl)

end

locale AfterExt_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s_locale =
  AfterExt_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale
  \<open>\<lambda>r s. if length r = lenL \<and> length s = lenR then \<lfloor>r @ s\<rfloor> else \<diamond>\<close>
  for lenL lenR :: nat

sublocale AfterExt_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s_locale \<subseteq> After_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s_locale
  by unfold_locales

locale OpSemTransitions_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s_locale =
  OpSemTransitions_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale
  \<open>\<lambda>r s. if length r = lenL \<and> length s = lenR then \<lfloor>r @ s\<rfloor> else \<diamond>\<close>
  for lenL lenR :: nat

sublocale OpSemTransitions_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s_locale \<subseteq> AfterExt_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s_locale
  by unfold_locales


(*<*)
end
  (*>*)