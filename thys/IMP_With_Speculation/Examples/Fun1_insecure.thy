subsection "Proof"
theory Fun1_insecure
imports Fun1
begin


subsubsection "Concrete leak"

definition "PC \<equiv> {0..6}"

definition "same_xx cfg3 cfgs3 cfg4 cfgs4 \<equiv> 
 vstore (getVstore (stateOf cfg3)) xx = vstore (getVstore (stateOf cfg4)) xx \<and>
 (\<forall>cfg3'\<in>set cfgs3. vstore (getVstore (stateOf cfg3')) xx = vstore (getVstore (stateOf cfg3)) xx) \<and> 
 (\<forall>cfg4'\<in>set cfgs4. vstore (getVstore (stateOf cfg4')) xx = vstore (getVstore (stateOf cfg4)) xx)"

(* two possible program traces for normal execution*)
definition "trueProg = {2,3,4,5,6}"
definition "falseProg = {2,3,5,6}"


(*pstate *)
definition "pstate\<^sub>1 \<equiv> update pstate\<^sub>0 [3]"
definition "pstate\<^sub>2 \<equiv> update pstate\<^sub>1 [5,5]"

lemmas pstate_def = pstate\<^sub>1_def pstate\<^sub>2_def

(*heap*)
(*provide different memories*)
fun hh\<^sub>3:: "nat \<Rightarrow> int" where 
"hh\<^sub>3 x =  (if x = (nat NN + 1) then 5 else 0)"

definition "h\<^sub>3 \<equiv>(Heap hh\<^sub>3)"

fun hh\<^sub>4:: "nat \<Rightarrow> int" where 
"hh\<^sub>4 x = (if x = (nat NN + 1) then 6 else 0)"

definition "h\<^sub>4 \<equiv>(Heap hh\<^sub>4)"

lemmas h_def = h\<^sub>3_def h\<^sub>4_def hh\<^sub>3.simps hh\<^sub>4.simps

(*used to show difference in heap vals*)
lemma ss_neq_aux1:"nat(5 * 512) \<noteq> nat (6 * 512)" by auto
lemma ss_neq_aux2:"nat(3 * 512) \<noteq> nat (5 * 512)" by auto
lemmas ss_neq = ss_neq_aux1 ss_neq_aux2
(*pointer*)
definition "p \<equiv> nat size_aa1 + nat size_aa2"

(*vstore and reads*)

definition "vs\<^sub>1 \<equiv> (vs\<^sub>0(xx := NN + 1))"


definition "vs\<^sub>2 \<equiv> (vs\<^sub>1(tt := 0))"

definition "aa1\<^sub>i \<equiv> array_loc aa1 (nat (vs\<^sub>2 xx)) avst'"

(*divergence between 3 and 4*)

definition "aa2\<^sub>v\<^sub>s\<^sub>3 \<equiv> array_loc aa2 (nat (hh\<^sub>3 aa1\<^sub>i * 512)) avst'"

definition "vs\<^sub>3\<^sub>3 = vs\<^sub>2(tt := hh\<^sub>3 aa2\<^sub>v\<^sub>s\<^sub>3)"

(**)
definition "aa2\<^sub>v\<^sub>s\<^sub>4 \<equiv> array_loc aa2 (nat (hh\<^sub>4 aa1\<^sub>i * 512)) avst'"

definition "vs\<^sub>3\<^sub>4 = vs\<^sub>2(tt := hh\<^sub>4 aa2\<^sub>v\<^sub>s\<^sub>4)"

lemmas reads\<^sub>m_def = aa1\<^sub>i_def aa2\<^sub>v\<^sub>s\<^sub>3_def aa2\<^sub>v\<^sub>s\<^sub>4_def
lemmas vs_def = vs\<^sub>0.simps vs\<^sub>1_def vs\<^sub>2_def vs\<^sub>3\<^sub>3_def vs\<^sub>3\<^sub>4_def


(*states*)
definition "s\<^sub>0\<^sub>3 \<equiv> (State (Vstore vs\<^sub>0) avst' h\<^sub>3 p)"
definition "s\<^sub>1\<^sub>3 \<equiv> (State (Vstore vs\<^sub>1) avst' h\<^sub>3 p)"
definition "s\<^sub>2\<^sub>3 \<equiv> (State (Vstore vs\<^sub>2) avst' h\<^sub>3 p)"
definition "s\<^sub>3\<^sub>3 \<equiv> (State (Vstore vs\<^sub>3\<^sub>3) avst' h\<^sub>3 p)"

definition "s\<^sub>0\<^sub>4 \<equiv> (State (Vstore vs\<^sub>0) avst' h\<^sub>4 p)"
definition "s\<^sub>1\<^sub>4 \<equiv> (State (Vstore vs\<^sub>1) avst' h\<^sub>4 p)"
definition "s\<^sub>2\<^sub>4 \<equiv> (State (Vstore vs\<^sub>2) avst' h\<^sub>4 p)"
definition "s\<^sub>3\<^sub>4 \<equiv> (State (Vstore vs\<^sub>3\<^sub>4) avst' h\<^sub>4 p)"

lemmas s_def = s\<^sub>0\<^sub>3_def s\<^sub>1\<^sub>3_def s\<^sub>2\<^sub>3_def s\<^sub>3\<^sub>3_def 
               s\<^sub>0\<^sub>4_def s\<^sub>1\<^sub>4_def s\<^sub>2\<^sub>4_def s\<^sub>3\<^sub>4_def

(*s3 stateA's*)
definition "(s3\<^sub>0:: stateO) \<equiv> (pstate\<^sub>0, (Config 0 s\<^sub>0\<^sub>3), [], repeat (NN+1), repeat (NN+1), {})"
definition "(s3\<^sub>1:: stateO) \<equiv> (pstate\<^sub>0, (Config 1 s\<^sub>0\<^sub>3), [], repeat (NN+1), repeat (NN+1), {})"
definition "(s3\<^sub>2:: stateO) \<equiv> (pstate\<^sub>0, (Config 2 s\<^sub>1\<^sub>3), [], repeat (NN+1), repeat (NN+1), {})"
definition "(s3\<^sub>3:: stateO) \<equiv> (pstate\<^sub>0, (Config 3 s\<^sub>2\<^sub>3), [], repeat (NN+1), repeat (NN+1), {})"
definition "(s3\<^sub>4:: stateO) \<equiv> (pstate\<^sub>1, (Config 5 s\<^sub>2\<^sub>3), [Config 4 s\<^sub>2\<^sub>3], repeat (NN+1), repeat (NN+1), {})"
definition "(s3\<^sub>5:: stateO) \<equiv> (pstate\<^sub>1, (Config 5 s\<^sub>2\<^sub>3), [Config 5 s\<^sub>3\<^sub>3], repeat (NN+1), repeat (NN+1), {aa2\<^sub>v\<^sub>s\<^sub>3, aa1\<^sub>i})"
definition "(s3\<^sub>6:: stateO) \<equiv> (pstate\<^sub>2, (Config 5 s\<^sub>2\<^sub>3), [], repeat (NN+1), repeat (NN+1), {aa2\<^sub>v\<^sub>s\<^sub>3, aa1\<^sub>i})"
definition "(s3\<^sub>7:: stateO) \<equiv> (pstate\<^sub>2, (Config 6 s\<^sub>2\<^sub>3), [], repeat (NN+1), repeat (NN+1), {aa2\<^sub>v\<^sub>s\<^sub>3, aa1\<^sub>i})"

lemmas s3_def = s3\<^sub>0_def s3\<^sub>1_def s3\<^sub>2_def s3\<^sub>3_def s3\<^sub>4_def s3\<^sub>5_def s3\<^sub>6_def s3\<^sub>7_def

lemmas state_def = s_def h_def vs_def reads\<^sub>m_def pstate_def avst_defs


(*s3 transition list*)
definition "s3_trans \<equiv> [s3\<^sub>0, s3\<^sub>1, s3\<^sub>2, s3\<^sub>3, s3\<^sub>4, s3\<^sub>5, s3\<^sub>6, s3\<^sub>7]"
lemmas s3_trans_defs = s3_trans_def s3_def 

lemma hd_s3_trans[simp]: "hd s3_trans = s3\<^sub>0" by (simp add: s3_trans_def)
lemma s3_trans_nemp[simp]: "s3_trans \<noteq> []" by (simp add: s3_trans_def)


(*transitions*)
lemma s3\<^sub>0\<^sub>1[simp]:"s3\<^sub>0 \<rightarrow>S s3\<^sub>1"
  unfolding s3_def
  using nonspec_normal
  by simp

lemma s3\<^sub>1\<^sub>2[simp]:"s3\<^sub>1 \<rightarrow>S s3\<^sub>2"
  unfolding s3_def state_def
  using nonspec_normal
  by simp

lemma s3\<^sub>2\<^sub>3[simp]:"s3\<^sub>2 \<rightarrow>S s3\<^sub>3"
  unfolding s3_def state_def
  by (simp add: finalM_iff)

lemma s3\<^sub>3\<^sub>4[simp]:"s3\<^sub>3 \<rightarrow>S s3\<^sub>4"
  unfolding s3_def state_def
  using nonspec_mispred
  by (simp add: finalM_iff)

lemma s3\<^sub>4\<^sub>5[simp]:"s3\<^sub>4 \<rightarrow>S s3\<^sub>5"
  unfolding s3_def state_def
  using spec_normal
  by (simp_all add: finalM_iff, blast) 

lemma s3\<^sub>5\<^sub>6[simp]:"s3\<^sub>5 \<rightarrow>S s3\<^sub>6"
  unfolding s3_def state_def
  using spec_resolve
  by simp

lemma s3\<^sub>6\<^sub>7[simp]:"s3\<^sub>6 \<rightarrow>S s3\<^sub>7"
  unfolding s3_def state_def
  using nonspec_normal
  by simp

lemma finalS_s3\<^sub>7[simp]:"finalS s3\<^sub>7"
  unfolding finalS_def final_def s3_def
  by (simp add: stepS_endPC)

lemmas s3_trans_simps = s3\<^sub>0\<^sub>1 s3\<^sub>1\<^sub>2 s3\<^sub>2\<^sub>3 s3\<^sub>3\<^sub>4 s3\<^sub>4\<^sub>5 s3\<^sub>5\<^sub>6 s3\<^sub>6\<^sub>7

(*s4 stateA's*)
definition "(s4\<^sub>0:: stateO) \<equiv> (pstate\<^sub>0, (Config 0 s\<^sub>0\<^sub>4), [], repeat (NN+1), repeat (NN+1), {})"
definition "(s4\<^sub>1:: stateO) \<equiv> (pstate\<^sub>0, (Config 1 s\<^sub>0\<^sub>4), [], repeat (NN+1), repeat (NN+1), {})"
definition "(s4\<^sub>2:: stateO) \<equiv> (pstate\<^sub>0, (Config 2 s\<^sub>1\<^sub>4), [], repeat (NN+1), repeat (NN+1), {})"
definition "(s4\<^sub>3:: stateO) \<equiv> (pstate\<^sub>0, (Config 3 s\<^sub>2\<^sub>4), [], repeat (NN+1), repeat (NN+1), {})"
definition "(s4\<^sub>4:: stateO) \<equiv> (pstate\<^sub>1, (Config 5 s\<^sub>2\<^sub>4), [Config 4 s\<^sub>2\<^sub>4], repeat (NN+1), repeat (NN+1), {})"
definition "(s4\<^sub>5:: stateO) \<equiv> (pstate\<^sub>1, (Config 5 s\<^sub>2\<^sub>4), [Config 5 s\<^sub>3\<^sub>4], repeat (NN+1), repeat (NN+1), {aa2\<^sub>v\<^sub>s\<^sub>4, aa1\<^sub>i})"
definition "(s4\<^sub>6:: stateO) \<equiv> (pstate\<^sub>2, (Config 5 s\<^sub>2\<^sub>4), [], repeat (NN+1), repeat (NN+1), {aa2\<^sub>v\<^sub>s\<^sub>4, aa1\<^sub>i})"
definition "(s4\<^sub>7:: stateO) \<equiv> (pstate\<^sub>2, (Config 6 s\<^sub>2\<^sub>4), [], repeat (NN+1), repeat (NN+1), {aa2\<^sub>v\<^sub>s\<^sub>4, aa1\<^sub>i})"

lemmas s4_def = s4\<^sub>0_def s4\<^sub>1_def s4\<^sub>2_def s4\<^sub>3_def s4\<^sub>4_def s4\<^sub>5_def s4\<^sub>6_def s4\<^sub>7_def


(*s4 transition list*)
definition "s4_trans \<equiv> [s4\<^sub>0, s4\<^sub>1, s4\<^sub>2, s4\<^sub>3, s4\<^sub>4, s4\<^sub>5, s4\<^sub>6, s4\<^sub>7]"
lemmas s4_trans_defs = s4_trans_def s4_def

lemma hd_s4_trans[simp]: "hd s4_trans = s4\<^sub>0" by (simp add: s4_trans_def)
lemma s4_trans_nemp[simp]: "s4_trans \<noteq> []" by (simp add: s4_trans_def)


(*transitions*)
lemma s4\<^sub>0\<^sub>1[simp]:"s4\<^sub>0 \<rightarrow>S s4\<^sub>1"
  unfolding s4_def
  using nonspec_normal
  by simp

lemma s4\<^sub>1\<^sub>2[simp]:"s4\<^sub>1 \<rightarrow>S s4\<^sub>2"
  unfolding s4_def state_def
  using nonspec_normal
  by simp

lemma s4\<^sub>2\<^sub>4[simp]:"s4\<^sub>2 \<rightarrow>S s4\<^sub>3"
  unfolding s4_def state_def
  using nonspec_normal
  by (simp add: finalM_iff)

lemma s4\<^sub>3\<^sub>4[simp]:"s4\<^sub>3 \<rightarrow>S s4\<^sub>4"
  unfolding s4_def state_def
  using nonspec_mispred
  by (simp add: finalM_iff)

lemma s4\<^sub>4\<^sub>5[simp]:"s4\<^sub>4 \<rightarrow>S s4\<^sub>5"
  unfolding s4_def state_def
  using spec_normal 
  by (simp add: finalM_iff, blast)

lemma s4\<^sub>5\<^sub>6[simp]:"s4\<^sub>5 \<rightarrow>S s4\<^sub>6"
  unfolding s4_def state_def
  using spec_resolve
  by simp

lemma s4\<^sub>6\<^sub>7[simp]:"s4\<^sub>6 \<rightarrow>S s4\<^sub>7"
  unfolding s4_def state_def
  using nonspec_normal
  by simp

lemma finalS_s4\<^sub>7[simp]:"finalS s4\<^sub>7"
  unfolding finalS_def final_def s4_def
  by (simp add: stepS_endPC)


lemmas s4_trans_simps = s4\<^sub>0\<^sub>1 s4\<^sub>1\<^sub>2 s4\<^sub>2\<^sub>4 s4\<^sub>3\<^sub>4 s4\<^sub>4\<^sub>5 s4\<^sub>5\<^sub>6 s4\<^sub>6\<^sub>7



subsubsection "Auxillary lemmas for disproof"
lemma validS_s3_trans[simp]:"Opt.validS s3_trans"
  unfolding Opt.validS_def validTransO.simps s3_trans_def
  apply safe  
  subgoal for i using cases_5[of i] 
    by(elim disjE, simp_all) .


lemma validS_s4_trans[simp]:"Opt.validS s4_trans"
  unfolding Opt.validS_def validTransO.simps s4_trans_def
  apply safe
  subgoal for i using cases_5[of i] 
  by(elim disjE, simp_all) .


lemma finalS_s3[simp]:"finalS (last s3_trans)" by (simp add: s3_trans_def)
lemma finalS_s4[simp]:"finalS (last s4_trans)" by (simp add: s4_trans_def)

lemma filter_s3[simp]:"(filter isIntO (butlast s3_trans)) = (butlast s3_trans)"
  unfolding s3_trans_def finalS_def final_def
  using s3_trans_simps validTransO.simps validTransO_iff_nextS 
  by (smt (verit) butlast.simps(2) filter.simps(1,2) isIntO.elims(3))

lemma filter_s4[simp]:"(filter isIntO (butlast s4_trans)) = (butlast s4_trans)"
  unfolding s4_trans_def finalS_def final_def
  using s4_trans_simps validTransO.simps validTransO_iff_nextS 
  by (smt (verit) butlast.simps(2) filter.simps(1,2) isIntO.elims(3))

lemma S_s3_trans[simp]:"Opt.S s3_trans = [s\<^sub>0\<^sub>3]"
  apply (simp add: Opt.S_def filtermap_def)
  unfolding s3_trans_defs by simp

lemma S_s4_trans[simp]:"Opt.S s4_trans = [s\<^sub>0\<^sub>4]"
  apply (simp add: Opt.S_def filtermap_def)
  unfolding s4_trans_defs by simp


lemma finalB_noStep[simp]:"\<And>s1'. finalB (cfg1, ibT1, ibUT1) \<Longrightarrow> (cfg1, ibT1, ibUT1, ls1) \<rightarrow>N s1' \<Longrightarrow> False"
  unfolding finalN_def final_def finalB_eq_finalN by auto

subsubsection "Disproof of fun1"
(*DISPROOF*)
fun common_memory::"config \<Rightarrow> config \<Rightarrow> bool" where 
"common_memory cfg1 cfg2 =
 (let h1 = (getHheap (stateOf cfg1)); 
      h2 = (getHheap (stateOf cfg2)) in
 ((\<forall>x\<in>read_add. h1 x = h2 x \<and> h1 x = 0) \<and>
  (getAvstore (stateOf cfg1)) = avst' \<and>
  (getAvstore (stateOf cfg2)) = avst'))"
(*for proof ease*)
lemma heap_eq0[simp]: "\<forall>x. x \<noteq> Suc NN \<longrightarrow> hh1' x = hh2' x \<and> hh1' x = 0 \<Longrightarrow> hh2' NN = 0" 
  by (metis n_not_Suc_n)
lemma heap1_eq0[simp]:"\<forall>x. x \<noteq> Suc NN \<longrightarrow> hh1' x = hh2' x \<and> hh1' x = 0 \<Longrightarrow>
               vs2 xx < NN \<Longrightarrow>
               hh2' (nat (vs2 xx)) = 0"
  using le_less_Suc_eq nat_le_eq_zle nat_less_eq_zless 
  by (metis lessI nat_int order.asym)

fun \<Gamma>_inv::"stateV \<Rightarrow> state list \<Rightarrow> stateV \<Rightarrow> state list \<Rightarrow> bool" where
"\<Gamma>_inv (cfg1,ibT1,ibUT1,ls1) sl1 (cfg2,ibT2,ibUT2,ls2) sl2 = 
(
 (pcOf cfg1 = pcOf cfg2) \<and> 

 (pcOf cfg1 < 2 \<longrightarrow> ibUT1 \<noteq> LNil \<and> ibUT2 \<noteq> LNil) \<and> 

 (pcOf cfg1 > 2 \<longrightarrow> same_var_val tt 0 cfg1 cfg2) \<and>

 (pcOf cfg1 > 1 \<longrightarrow> (same_var xx cfg1 cfg2) \<and>

                    (vs\<^sub>i_t cfg1 \<longrightarrow> pcOf cfg1 \<in> trueProg) \<and>

                    (vs\<^sub>i_f cfg1 \<longrightarrow> pcOf cfg1 \<in> falseProg))
 \<and>
 ls1 = ls2 \<and>

 pcOf cfg1 \<in> PC \<and>
 common_memory cfg1 cfg2
)"

declare \<Gamma>_inv.simps[simp del]
lemmas \<Gamma>_def = \<Gamma>_inv.simps
lemmas \<Gamma>_defs = \<Gamma>_def common_memory.simps PC_def aa1\<^sub>i_def
                trueProg_def falseProg_def same_var_val_def same_var_def

lemma \<Gamma>_implies:"\<Gamma>_inv (cfg1,ibT1, ibUT1,ls1) sl1 (cfg2,ibT2,ibUT2,ls2) sl2 \<Longrightarrow> 
  pcOf cfg1 \<le> 6 \<and> pcOf cfg2 \<le> 6 \<and> 

  (pcOf cfg1 = 4 \<longrightarrow> vs\<^sub>i_t cfg1) \<and>
  (pcOf cfg2 = 4 \<longrightarrow> vs\<^sub>i_t cfg2) \<and>
  (pcOf cfg1 > 1 \<longrightarrow> vs\<^sub>i_t cfg1 \<longleftrightarrow> vs\<^sub>i_t cfg2) \<and>

  (finalB (cfg1,ibT1,ibUT1) \<longleftrightarrow> pcOf cfg1 = 6) \<and>
  (finalB (cfg2,ibT2,ibUT2) \<longleftrightarrow> pcOf cfg2 = 6)
"
  unfolding \<Gamma>_defs
  apply(elim conjE, intro conjI)
  subgoal using atLeastAtMost_iff by blast
  subgoal using vs_xx_cases[of cfg2] by (elim disjE, simp_all) 
  subgoal apply (rule impI,simp) using vs_xx_cases[of cfg1] by (elim disjE, simp_all)
  subgoal apply (rule impI,simp) using vs_xx_cases[of cfg2] vs\<^sub>i_defs by (elim disjE, simp_all)
  subgoal by (simp add: vs\<^sub>i_defs)
  using finalB_pcOf_iff 
   apply (metis atLeastAtMost_iff one_less_numeral_iff semiring_norm(76))
  using finalB_pcOf_iff
  by (metis atLeastAtMost_iff numeral_One numeral_less_iff semiring_norm(76))

(*istate*)
lemma istateO_s3[simp]:"istateO s3\<^sub>0" unfolding s3_def state_def by simp
lemma istateO_s4[simp]:"istateO s4\<^sub>0" unfolding s4_def state_def by simp

(*validFromS*)
lemma validFromS_s3[simp]:"Opt.validFromS s3\<^sub>0 s3_trans"
  unfolding Opt.validFromS_def by simp

lemma validFromS_s4[simp]:"Opt.validFromS s4\<^sub>0 s4_trans"
  unfolding Opt.validFromS_def by simp

(*completedFromO*)

lemma completedFromO_s3[simp]:"completedFromO s3\<^sub>0 s3_trans"
  unfolding Opt.completedFrom_def by simp

lemma completedFromO_s4[simp]:"completedFromO s4\<^sub>0 s4_trans"
  unfolding Opt.completedFrom_def by simp

(*Act eq*)
lemma Act_eq[simp]:"Opt.A s3_trans = Opt.A s4_trans"
  apply (simp add: Opt.A_def filtermap_def)
  unfolding s3_trans_defs s4_trans_defs
  by simp

lemma aa2_neq:"aa2\<^sub>v\<^sub>s\<^sub>3 \<noteq> aa2\<^sub>v\<^sub>s\<^sub>4"
  unfolding vs_def reads\<^sub>m_def avst_defs h_def array_loc_def  
  by (simp add: avst_defs array_base_def split: if_splits)

lemma aa1_neq:"aa2\<^sub>v\<^sub>s\<^sub>3 \<noteq> aa1\<^sub>i"
  apply(rule notI)
  unfolding vs_def reads\<^sub>m_def avst_defs h_def array_loc_def  
  by (simp add: avst_defs array_base_def split: if_splits)

lemma aa1_neq2:"aa2\<^sub>v\<^sub>s\<^sub>4 \<noteq> aa1\<^sub>i"
  apply(rule notI)
  unfolding vs_def reads\<^sub>m_def avst_defs h_def array_loc_def  
  by (simp add: avst_defs array_base_def split: if_splits)

(*Obs neq*)
lemma Obs_neq[simp]:"Opt.O s3_trans \<noteq> Opt.O s4_trans"
  apply (simp add: Opt.O_def filtermap_def)
  unfolding s3_trans_def s4_trans_def apply clarsimp
  unfolding s3_trans_defs s4_trans_defs apply simp
  using aa2_neq aa1_neq aa1_neq2 by blast
   
  

lemma \<Gamma>_init[simp]:"\<And>s1 s2. istateV s1 \<Longrightarrow> corrState s1 s3\<^sub>0 \<Longrightarrow> istateV s2 \<Longrightarrow> corrState s2 s4\<^sub>0 \<Longrightarrow> \<Gamma>_inv s1 [s\<^sub>0\<^sub>3] s2 [s\<^sub>0\<^sub>4]"
  subgoal for s1 s2 apply(cases s1, cases s2, simp) 
    unfolding s3_def s4_def s_def h_def by (auto simp: \<Gamma>_defs) .

lemma val_neq_1:"nat (hh2' (nat (vs2 xx)) * 512) \<noteq> 1" 
  by (smt (z3) nat_less_eq_zless nat_one_as_int)


(*unwindSD*)
lemma unwindSD[simp]:"Rel_Sec.unwindSDCond validTransV istateV isSecV getSecV isIntV getIntV \<Gamma>_inv"
unfolding unwindSDCond_def
proof(intro allI, rule impI, elim conjE,intro conjI)
      fix ss1 ss2 sl1 sl2
      assume "reachV ss1" "reachV ss2" 
       and \<Gamma>:"\<Gamma>_inv ss1 sl1 ss2 sl2"

      obtain cfg1 ibT1 ibUT1 ls1 where ss1: "ss1 = (cfg1, ibT1, ibUT1, ls1)"
        by (cases ss1, auto) 
      obtain cfg2 ibT2 ibUT2 ls2 where ss2: "ss2 = (cfg2, ibT2, ibUT2, ls2)"
        by (cases ss2, auto) 
      note ss = ss1 ss2 

      obtain pc1 vs1 avst1 h1 p1 where 
        cfg1: "cfg1 = Config pc1 (State (Vstore vs1) avst1 h1 p1)"
        by (cases cfg1) (metis state.collapse vstore.collapse)
      obtain pc2 vs2 avst2 h2 p2 where 
        cfg2: "cfg2 = Config pc2 (State (Vstore vs2) avst2 h2 p2)"
        by (cases cfg2) (metis state.collapse vstore.collapse)
      note cfg = cfg1 cfg2

      obtain hh1 where h1: "h1 = Heap hh1" by(cases h1, auto)
      obtain hh2 where h2: "h2 = Heap hh2" by(cases h2, auto)
      note hh = h1 h2

      show "isIntV ss1 = isIntV ss2" 
        using  \<Gamma> unfolding isIntV.simps ss
        unfolding \<Gamma>_defs
        using vs_xx_cases[of cfg1]
        apply (elim disjE) by simp_all

      then have finalB:"finalB (cfg1, ibT1, ibUT1) = finalB (cfg2, ibT2, ibUT2)"
        unfolding isIntV.simps finalN_iff_finalB ss by blast

      show "\<not> isIntV ss1 \<longrightarrow> move1 \<Gamma>_inv ss1 sl1 ss2 sl2 \<and> move2 \<Gamma>_inv ss1 sl1 ss2 sl2"
        apply(unfold ss, auto)
        subgoal unfolding move1_def finalB_defs by auto
        subgoal unfolding finalB 
                unfolding move2_def finalB_defs by auto . 

      show "isIntV ss1 \<longrightarrow> getActV ss1 = getActV ss2 \<longrightarrow> getObsV ss1 = getObsV ss2 \<and> move12 \<Gamma>_inv ss1 sl1 ss2 sl2"
      proof(unfold ss isIntV.simps finalN_iff_finalB, intro impI, rule conjI)
        assume final:"\<not> finalB (cfg1, ibT1, ibUT1)" and
              getAct:"getActV (cfg1, ibT1, ibUT1, ls1) = getActV (cfg2, ibT2, ibUT2, ls2)"
        have not6:"pc1 = 6 \<Longrightarrow> False"
          using cfg final \<Gamma>
          by simp

        show "getObsV (cfg1, ibT1, ibUT1, ls1) = getObsV (cfg2, ibT2, ibUT2, ls2)" 
          using \<Gamma> getAct unfolding ss 
          apply-apply(frule \<Gamma>_implies, elim conjE)
          using cases_5[of "pcOf cfg1"] cases_5[of "pcOf cfg2"] 
          by(elim disjE, simp_all add: \<Gamma>_defs final)

        show "move12 \<Gamma>_inv (cfg1, ibT1, ibUT1, ls1) sl1 (cfg2, ibT2, ibUT2, ls2) sl2" 
        unfolding move12_def validEtransO.simps 
      proof(intro allI, rule impI, elim conjE,unfold validTransV.simps isSecV_iff getSecV.simps fst_conv)
          fix ss1' ss2' sl1' sl2'

          assume v: "(cfg1, ibT1, ibUT1, ls1) \<rightarrow>N ss1'" "(cfg2, ibT2, ibUT2, ls2) \<rightarrow>N ss2'" and
               sec: "pcOf cfg1 \<noteq> 0 \<and> sl1 = sl1' \<or> pcOf cfg1 = 0 \<and> sl1 = stateOf cfg1 # sl1'"
                    "pcOf cfg2 \<noteq> 0 \<and> sl2 = sl2' \<or> pcOf cfg2 = 0 \<and> sl2 = stateOf cfg2 # sl2'"
          
          obtain cfg1' ibT1' ibUT1' ls1' where ss1': "ss1' = (cfg1', ibT1', ibUT1', ls1')"
            by (cases ss1', auto) 
          obtain cfg2' ibT2' ibUT2' ls2' where ss2': "ss2' = (cfg2', ibT2', ibUT2', ls2')"
            by (cases ss2', auto)

          obtain pc1' vs1' avst1' h1' p1' where 
            cfg1': "cfg1' = Config pc1' (State (Vstore vs1') avst1' h1' p1')"
            by (cases cfg1') (metis state.collapse vstore.collapse)
          obtain pc2' vs2' avst2' h2' p2' where 
            cfg2': "cfg2' = Config pc2' (State (Vstore vs2') avst2' h2' p2')"
            by (cases cfg2') (metis state.collapse vstore.collapse)
          note cfg = cfg cfg1' cfg2'

          obtain hh1' where h1': "h1' = Heap hh1'" by(cases h1', auto)
          obtain hh2' where h2': "h2' = Heap hh2'" by(cases h2', auto)
          note hh = hh h1' h2'

          note ss = ss1 ss2 ss1' ss2'
          have v':"(cfg1, ibT1, ibUT1) \<rightarrow>B (cfg1', ibT1', ibUT1')" using v unfolding ss by simp
          then have v1:"nextB (cfg1, ibT1, ibUT1) = (cfg1', ibT1', ibUT1')" using stepB_nextB by auto

          have v'':"(cfg2, ibT2, ibUT2) \<rightarrow>B (cfg2', ibT2', ibUT2')" using v unfolding ss by simp
          then have v2:"nextB (cfg2, ibT2, ibUT2) = (cfg2', ibT2', ibUT2')" using stepB_nextB by auto
          note valid = v' v1 v'' v2 

          have ls1':"ls1' = ls1 \<union> readLocs cfg1" using v unfolding ss by simp
          have ls2':"ls2' = ls2 \<union> readLocs cfg2" using v unfolding ss by simp
          note ls = ls1' ls2'


          note \<Gamma>_simps = cfg ls vs\<^sub>i_defs hh array_loc_def 
                          array_base_def state_def PC_def

          show "\<Gamma>_inv ss1' sl1' ss2' sl2'" 
            using \<Gamma> valid getAct
            unfolding ss apply-apply(frule \<Gamma>_implies)
            using cases_5[of "pc1"] not6 apply(elim disjE, simp_all)
            unfolding \<Gamma>_def ss
            prefer 4 subgoal using vs_xx_cases[of cfg1]
            by (elim disjE, unfold \<Gamma>_defs, auto simp add: \<Gamma>_simps) 
            subgoal by (unfold \<Gamma>_defs, auto simp add: \<Gamma>_simps) 
            subgoal by (unfold \<Gamma>_defs, auto simp add: \<Gamma>_simps) 
            subgoal by (unfold \<Gamma>_defs, auto simp add: \<Gamma>_simps)
            subgoal using val_neq_1 apply (unfold \<Gamma>_defs, auto simp add: \<Gamma>_simps) 
              using val_neq_1 by (metis NN_suc add_left_cancel nat_int) 
            subgoal by (unfold \<Gamma>_defs, auto simp add: \<Gamma>_simps) 
            subgoal by (unfold \<Gamma>_defs, auto simp add: \<Gamma>_simps) .
        qed
      qed
    qed


theorem "\<not>rsecure"
  apply(rule unwindSD_rsecure[of s3\<^sub>0 s3_trans s4\<^sub>0 s4_trans \<Gamma>_inv]) 
  by simp_all

end