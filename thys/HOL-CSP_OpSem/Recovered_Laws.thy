(*<*)
\<comment>\<open> ******************************************************************** 
 * Project         : HOL-CSP_OpSem - Operational semantics for HOL-CSP
 *
 * Author          : Benoît Ballenghien, Burkhart Wolff.
 *
 * This file       : Recovered laws pretty printed
 *
 * Copyright (c) 2025 Université Paris-Saclay, France
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *     * Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 *
 *     * Neither the name of the copyright holders nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 ******************************************************************************\<close>
(*>*)

chapter \<open> Recovered Laws pretty printed\<close>

(*<*)
theory  Recovered_Laws
  imports Operational_Semantics_Laws "HOL-Library.LaTeXsugar"
begin
  (*>*)


section \<open>General Case\<close>

text \<open>This is the general case, working for \<^term>\<open>(\<sqsubseteq>\<^sub>F\<^sub>D)\<close> and \<^term>\<open>(\<sqsubseteq>\<^sub>D\<^sub>T)\<close>.\<close>

context OpSemTransitionsAll begin

paragraph \<open>Absorbency rules\<close>
text \<open>\begin{center}
      @{thm[mode=Rule] ev_trans_\<tau>_trans} \qquad
      @{thm[mode=Rule] \<tau>_trans_ev_trans}
      
      @{thm[mode=Rule] tick_trans_\<tau>_trans} \qquad
      @{thm[mode=Rule] \<tau>_trans_tick_trans}
      \end{center}\<close>

paragraph \<open>\<^const>\<open>SKIP\<close> rule\<close>
text \<open>\begin{center}
      @{thm[mode=Axiom] SKIP_OpSem_rule}
      \end{center}\<close>

paragraph \<open>\<^term>\<open>e \<rightarrow> P\<close> rules\<close>
text \<open>\begin{center}
      @{thm[mode=Axiom] prefix_OpSem_rules(1)}

      @{thm[mode=Rule, eta_contract=false] prefix_OpSem_rules(2)}\qquad
      @{thm[mode=Rule, eta_contract=false] prefix_OpSem_rules(3)}
      \end{center}\<close>

paragraph \<open>\<^const>\<open>Ndet\<close> rules\<close>
text \<open>\begin{center}
      @{thm[mode=Axiom] Ndet_OpSem_rules(1)} \qquad
      @{thm[mode=Axiom] Ndet_OpSem_rules(2)}

      @{thm[mode=Rule, eta_contract=false] Ndet_OpSem_rules(3)}
      \end{center}\<close>

paragraph \<open>\<^term>\<open>\<mu> X. f X\<close> rule\<close>
text \<open>\begin{center}
      @{thm[mode=Rule, eta_contract=false] fix_point_OpSem_rule}
      \end{center}\<close>

paragraph \<open>\<^const>\<open>Det\<close> rules\<close>
text \<open>\begin{center}
      @{thm[mode=Rule, eta_contract=false] Det_OpSem_rules(1)} \qquad
      @{thm[mode=Rule, eta_contract=false] Det_OpSem_rules(2)}

      @{thm[mode=Rule, eta_contract=false] Det_OpSem_rules(3)} \qquad
      @{thm[mode=Rule, eta_contract=false] Det_OpSem_rules(4)}
      
      @{thm[mode=Rule, eta_contract=false] Det_OpSem_rules(5)} \qquad
      @{thm[mode=Rule, eta_contract=false] Det_OpSem_rules(6)}
      \end{center}\<close>

paragraph \<open>\<^const>\<open>Seq\<close> rules\<close>
text \<open>\begin{center}
      @{thm[mode=Rule, eta_contract=false] Seq_OpSem_rules(1)}

      @{thm[mode=Rule, eta_contract=false] Seq_OpSem_rules(2)} \qquad
      @{thm[mode=Rule, eta_contract=false] Seq_OpSem_rules(3)}
      \end{center}\<close>

paragraph \<open>\<^const>\<open>Hiding\<close> rules\<close>
text \<open>\begin{center}
      @{thm[mode=Rule, eta_contract=false] Hiding_OpSem_rules(1)} \qquad
      @{thm[mode=Rule, eta_contract=false] Hiding_OpSem_rules(2)}

      @{thm[mode=Rule, eta_contract=false] Hiding_OpSem_rules(3)} \qquad
      @{thm[mode=Rule, eta_contract=false] Hiding_OpSem_rules(4)}
      \end{center}\<close>

(* paragraph \<open>\<^const>\<open>Renaming\<close> rules\<close>
text \<open>\begin{center}
      @{thm[mode=Rule, eta_contract=false] prefix_OpSem_rules}
      \end{center}\<close> *)

paragraph \<open>\<^const>\<open>Sync\<close> rules\<close>
text \<open>\begin{center}
      @{thm[mode=Rule, eta_contract=false] Sync_OpSem_rules(1)} \qquad
      @{thm[mode=Rule, eta_contract=false] Sync_OpSem_rules(2)}

      @{thm[mode=Rule, eta_contract=false] Sync_OpSem_rules(3)} \qquad
      @{thm[mode=Rule, eta_contract=false] Sync_OpSem_rules(4)}

      @{thm[mode=Rule, eta_contract=false] Sync_OpSem_rules(5)}

      @{thm[mode=Rule, eta_contract=false] Sync_OpSem_rules(6)} \qquad
      @{thm[mode=Rule, eta_contract=false] Sync_OpSem_rules(7)}
    
      @{thm[mode=Axiom] Sync_OpSem_rules(8)}
      \end{center}\<close>

paragraph \<open>\<^const>\<open>Sliding\<close> rules\<close>
text \<open>\begin{center}
      @{thm[mode=Axiom] Sliding_OpSem_rules(1)} \qquad
      @{thm[mode=Rule, eta_contract=false] Sliding_OpSem_rules(2)}

      @{thm[mode=Rule, eta_contract=false] Sliding_OpSem_rules(3)} \qquad
      @{thm[mode=Rule, eta_contract=false] Sliding_OpSem_rules(4)}
      \end{center}\<close>

paragraph \<open>\<^const>\<open>Interrupt\<close> rules\<close>
text \<open>\begin{center}
      @{thm[mode=Rule, eta_contract=false] Interrupt_OpSem_rules(1)} \qquad
      @{thm[mode=Rule, eta_contract=false] Interrupt_OpSem_rules(2)} 

      @{thm[mode=Rule, eta_contract=false] Interrupt_OpSem_rules(3)} \qquad
      @{thm[mode=Rule, eta_contract=false] Interrupt_OpSem_rules(4)} 
      
      @{thm[mode=Rule, eta_contract=false] Interrupt_OpSem_rules(5)} \qquad
      @{thm[mode=Rule, eta_contract=false] Interrupt_OpSem_rules(6)} 
      \end{center}\<close>

paragraph \<open>\<^const>\<open>Throw\<close> rules\<close>
text \<open>\begin{center}
      @{thm[mode=Rule, eta_contract=false] Throw_OpSem_rules(1)} \qquad
      @{thm[mode=Rule, eta_contract=false] Throw_OpSem_rules(2)}

      @{thm[mode=Rule, eta_contract=false] Throw_OpSem_rules(3)} \qquad
      @{thm[mode=Rule, eta_contract=false] Throw_OpSem_rules(4)}
      \end{center}\<close>

end

context OpSemTransitionsAllDuplicated begin

paragraph \<open>\<^const>\<open>Renaming\<close> rules\<close>
text \<open>\begin{center}
      @{thm[mode=Rule, eta_contract=false] Renaming_OpSem_rules(1)}

      @{thm[mode=Rule, eta_contract=false] Renaming_OpSem_rules(2)} \qquad
      @{thm[mode=Rule, eta_contract=false] Renaming_OpSem_rules(3)}
      \end{center}\<close>

end


section \<open>Special Cases\<close>


subsection \<open>With the Refinement \<^term>\<open>(\<sqsubseteq>\<^sub>D\<^sub>T)\<close>\<close>

context OpSemDT begin

paragraph \<open>\<^const>\<open>Det\<close> rules\<close>
text \<open>\begin{center}
      @{thm[mode=Axiom] Ndet_OpSem_rules(1)[of P Q, folded \<tau>_trans_Det_is_\<tau>_trans_Ndet]} \qquad
      @{thm[mode=Axiom] Ndet_OpSem_rules(2)[of P Q, folded \<tau>_trans_Det_is_\<tau>_trans_Ndet]}
      \end{center}\<close>

paragraph \<open>\<^const>\<open>Sliding\<close> rules\<close>
text \<open>\begin{center}
      @{thm[mode=Axiom] Ndet_OpSem_rules(1)[of P Q, folded \<tau>_trans_Sliding_is_\<tau>_trans_Ndet]} \qquad
      @{thm[mode=Axiom] Ndet_OpSem_rules(2)[of P Q, folded \<tau>_trans_Sliding_is_\<tau>_trans_Ndet]}
      \end{center}\<close>

end


subsection \<open>With the Refinement \<^term>\<open>(\<sqsubseteq>\<^sub>F)\<close>\<close>

context OpSemF begin

paragraph \<open>Absorbency rules\<close>
text \<open>\begin{center}
      @{thm[mode=Rule] ev_trans_\<tau>_trans} \qquad
      @{thm[mode=Rule] \<tau>_trans_ev_trans}

      @{thm[mode=Rule] tick_trans_\<tau>_trans} \qquad
      @{thm[mode=Rule] \<tau>_trans_tick_trans}
      \end{center}\<close>

paragraph \<open>\<^const>\<open>SKIP\<close> rule\<close>
text \<open>\begin{center}
      @{thm[mode=Axiom] SKIP_OpSem_rule}
      \end{center}\<close>

paragraph \<open>\<^term>\<open>e \<rightarrow> P\<close> rules\<close>
text \<open>\begin{center}
      @{thm[mode=Axiom] prefix_OpSem_rules(1)}

      @{thm[mode=Rule, eta_contract=false] prefix_OpSem_rules(2)}\qquad
      @{thm[mode=Rule, eta_contract=false] prefix_OpSem_rules(3)}
      \end{center}\<close>

paragraph \<open>\<^const>\<open>Ndet\<close> rules\<close>
text \<open>\begin{center}
      @{thm[mode=Axiom] Ndet_OpSem_rules(1)} \qquad
      @{thm[mode=Axiom] Ndet_OpSem_rules(2)}

      @{thm[mode=Rule, eta_contract=false] Ndet_OpSem_rules(3)}
      \end{center}\<close>

paragraph \<open>\<^term>\<open>\<mu> X. f X\<close> rule\<close>
text \<open>\begin{center}
      @{thm[mode=Rule, eta_contract=false] fix_point_OpSem_rule}
      \end{center}\<close>

paragraph \<open>\<^const>\<open>Det\<close> rules\<close>
text \<open>\begin{center} 
      @{thm[mode=Rule, eta_contract=false] Det_OpSem_rules(1)} \qquad
      @{thm[mode=Rule, eta_contract=false] Det_OpSem_rules(2)}

      @{thm[mode=Rule, eta_contract=false] Det_OpSem_rules(3)} \qquad
      @{thm[mode=Rule, eta_contract=false] Det_OpSem_rules(4)}

      @{thm[mode=Rule, eta_contract=false] Det_OpSem_rules(5)} \qquad
      @{thm[mode=Rule, eta_contract=false] Det_OpSem_rules(6)}
      \end{center}\<close>

paragraph \<open>\<^const>\<open>Seq\<close> rules\<close>
text \<open>\begin{center}
      @{thm[mode=Rule, eta_contract=false] \<tau>_trans_SeqR}
      \end{center}\<close>

paragraph \<open>\<^const>\<open>Hiding\<close> rules\<close>
text \<open>\begin{center}
      @{thm[mode=Rule, eta_contract=false] Hiding_OpSem_rules(1)} \qquad
      @{thm[mode=Rule, eta_contract=false] Hiding_OpSem_rules(2)}

      @{thm[mode=Rule, eta_contract=false] Hiding_OpSem_rules(3)} \qquad
      @{thm[mode=Rule, eta_contract=false] Hiding_OpSem_rules(4)}
      \end{center}\<close>

(* paragraph \<open>\<^const>\<open>Renaming\<close> rules\<close>
text \<open>\begin{center}
      @{thm[mode=Rule, eta_contract=false] prefix_OpSem_rules}
      \end{center}\<close> *)

paragraph \<open>\<^const>\<open>Sync\<close> rules\<close>
text \<open>\begin{center}
      @{thm[mode=Rule, eta_contract=false] \<tau>_trans_SKIP_SyncL} \qquad
      @{thm[mode=Rule, eta_contract=false] \<tau>_trans_SKIP_SyncR}

      @{thm[mode=Axiom] tick_trans_SKIP_Sync_SKIP}
      \end{center}\<close>

paragraph \<open>\<^const>\<open>Sliding\<close> rules\<close>
text \<open>\begin{center}
      @{thm[mode=Axiom, eta_contract=false] Sliding_OpSem_rules(1)} \qquad
      @{thm[mode=Rule, eta_contract=false] Sliding_OpSem_rules(2)}

      @{thm[mode=Rule, eta_contract=false] Sliding_OpSem_rules(3)} \qquad
      @{thm[mode=Rule, eta_contract=false] Sliding_OpSem_rules(4)}
      \end{center}\<close>

paragraph \<open>\<^const>\<open>Interrupt\<close> rules\<close>
text \<open>\begin{center}
      @{thm[mode=Rule, eta_contract=false] tick_trans_InterruptL} \qquad
      @{thm[mode=Rule, eta_contract=false] tick_trans_InterruptR} 
      \end{center}\<close>

paragraph \<open>\<^const>\<open>Throw\<close> rules\<close>
text \<open>\begin{center}
      @{thm[mode=Rule, eta_contract=false] ev_trans_ThrowR_inside} \qquad
      @{thm[mode=Rule, eta_contract=false] tick_trans_ThrowL}
      \end{center}\<close>

end 

context OpSemFDuplicated begin

paragraph \<open>\<^const>\<open>Renaming\<close> rules\<close>
text \<open>\begin{center}
      @{thm[mode=Rule, eta_contract=false] tick_trans_Renaming}
      \end{center}\<close>

end


subsection \<open>With the Refinement \<^term>\<open>(\<sqsubseteq>\<^sub>T)\<close>\<close>

context OpSemT begin

paragraph \<open>Absorbency rules\<close>
text \<open>\begin{center}
      @{thm[mode=Rule] ev_trans_\<tau>_trans} \qquad
      @{thm[mode=Rule] \<tau>_trans_ev_trans}

      @{thm[mode=Rule] tick_trans_\<tau>_trans} \qquad
      @{thm[mode=Rule] \<tau>_trans_tick_trans}
      \end{center}\<close>

paragraph \<open>\<^const>\<open>SKIP\<close> rule\<close>
text \<open>\begin{center}
      @{thm[mode=Axiom] SKIP_OpSem_rule}
      \end{center}\<close>

paragraph \<open>\<^term>\<open>e \<rightarrow> P\<close> rules\<close>
text \<open>\begin{center}
      @{thm[mode=Axiom] prefix_OpSem_rules(1)}

      @{thm[mode=Rule, eta_contract=false] prefix_OpSem_rules(2)}\qquad
      @{thm[mode=Rule, eta_contract=false] prefix_OpSem_rules(3)}
      \end{center}\<close>

paragraph \<open>\<^const>\<open>Ndet\<close> rules\<close>
text \<open>\begin{center}
      @{thm[mode=Axiom] Ndet_OpSem_rules(1)} \qquad
      @{thm[mode=Axiom] Ndet_OpSem_rules(2)}

      @{thm[mode=Rule, eta_contract=false] Ndet_OpSem_rules(3)}
      \end{center}\<close>

paragraph \<open>\<^term>\<open>\<mu> X. f X\<close> rule\<close>
text \<open>\begin{center}
      @{thm[mode=Rule, eta_contract=false] fix_point_OpSem_rule}
      \end{center}\<close>

paragraph \<open>\<^const>\<open>Det\<close> rules\<close>
text \<open>\begin{center}
      @{thm[mode=Rule, eta_contract=false] Det_OpSem_rules(1)} \qquad
      @{thm[mode=Rule, eta_contract=false] Det_OpSem_rules(2)}

      @{thm[mode=Rule, eta_contract=false] Det_OpSem_rules(3)} \qquad
      @{thm[mode=Rule, eta_contract=false] Det_OpSem_rules(4)}
      
      @{thm[mode=Rule, eta_contract=false] Det_OpSem_rules(5)} \qquad
      @{thm[mode=Rule, eta_contract=false] Det_OpSem_rules(6)}
      \end{center}\<close>

paragraph \<open>\<^const>\<open>Seq\<close> rules\<close>
text \<open>\begin{center}
      @{thm[mode=Rule, eta_contract=false] \<tau>_trans_SeqR}
      \end{center}\<close>

paragraph \<open>\<^const>\<open>Hiding\<close> rules\<close>
text \<open>\begin{center}
      @{thm[mode=Rule, eta_contract=false] Hiding_OpSem_rules(1)} \qquad
      @{thm[mode=Rule, eta_contract=false] Hiding_OpSem_rules(2)}

      @{thm[mode=Rule, eta_contract=false] Hiding_OpSem_rules(3)} \qquad
      @{thm[mode=Rule, eta_contract=false] Hiding_OpSem_rules(4)}
      \end{center}\<close>

(* paragraph \<open>\<^const>\<open>Renaming\<close> rules\<close>
text \<open>\begin{center}
      @{thm[mode=Rule, eta_contract=false] prefix_OpSem_rules}
      \end{center}\<close> *)

paragraph \<open>\<^const>\<open>Sync\<close> rules\<close>
text \<open>\begin{center}
      @{thm[mode=Rule, eta_contract=false] \<tau>_trans_SKIP_SyncL} \qquad
      @{thm[mode=Rule, eta_contract=false] \<tau>_trans_SKIP_SyncR}

      @{thm[mode=Axiom] tick_trans_SKIP_Sync_SKIP}
      \end{center}\<close>

paragraph \<open>\<^const>\<open>Sliding\<close> rules\<close>
text \<open>\begin{center}
      @{thm[mode=Axiom] Sliding_OpSem_rules(1)} \qquad
      @{thm[mode=Rule, eta_contract=false] Sliding_OpSem_rules(2)}

      @{thm[mode=Rule, eta_contract=false] Sliding_OpSem_rules(3)} \qquad
      @{thm[mode=Rule, eta_contract=false] Sliding_OpSem_rules(4)}
      \end{center}\<close>

paragraph \<open>\<^const>\<open>Interrupt\<close> rules\<close>
text \<open>\begin{center}
      @{thm[mode=Rule, eta_contract=false] Interrupt_OpSem_rules(1)} \qquad
      @{thm[mode=Rule, eta_contract=false] Interrupt_OpSem_rules(2)} 

      @{thm[mode=Rule, eta_contract=false] Interrupt_OpSem_rules(3)} \qquad
      @{thm[mode=Rule, eta_contract=false] Interrupt_OpSem_rules(4)} 
      
      @{thm[mode=Rule, eta_contract=false] Interrupt_OpSem_rules(5)} \qquad
      @{thm[mode=Rule, eta_contract=false] Interrupt_OpSem_rules(6)} 
      \end{center}\<close>

paragraph \<open>\<^const>\<open>Throw\<close> rules\<close>
text \<open>\begin{center}
      @{thm[mode=Rule, eta_contract=false] ev_trans_ThrowR_inside} \qquad
      @{thm[mode=Rule, eta_contract=false] tick_trans_ThrowL}
      \end{center}\<close>


text \<open>Because we only look at the traces, we actully have the following results.\<close>

paragraph \<open>\<^const>\<open>Det\<close> rules\<close>
text \<open>\begin{center}
      @{thm[mode=Axiom] Ndet_OpSem_rules(1)[of P Q, folded \<tau>_trans_Det_is_\<tau>_trans_Ndet]} \qquad
      @{thm[mode=Axiom] Ndet_OpSem_rules(2)[of P Q, folded \<tau>_trans_Det_is_\<tau>_trans_Ndet]}
      \end{center}\<close>

paragraph \<open>\<^const>\<open>Sliding\<close> rules\<close>
text \<open>\begin{center}
      @{thm[mode=Axiom] Ndet_OpSem_rules(1)[of P Q, folded \<tau>_trans_Sliding_is_\<tau>_trans_Ndet]} \qquad
      @{thm[mode=Axiom] Ndet_OpSem_rules(2)[of P Q, folded \<tau>_trans_Sliding_is_\<tau>_trans_Ndet]}
      \end{center}\<close>

end

context OpSemTDuplicated begin

paragraph \<open>\<^const>\<open>Renaming\<close> rules\<close>
text \<open>\begin{center}
      @{thm[mode=Rule, eta_contract=false] tick_trans_Renaming}
      \end{center}\<close>


end



(*<*)
end 
(*>*)


