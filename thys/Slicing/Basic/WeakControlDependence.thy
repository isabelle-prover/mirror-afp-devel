header {* \isaheader{Weak control dependence} *}

theory WeakControlDependence imports PDG Postdomination begin

subsection {* Dynamic standard control dependence *}

subsubsection {* Definition and some lemmas *}

definition (in StrongPostdomination)
  dyn_weak_control_dependence :: "'node \<Rightarrow> 'node \<Rightarrow> 'edge list \<Rightarrow> bool" 
  ("_ weakly controls _ via _" [51,0,0])
where dyn_weak_control_dependence_def:"n weakly controls n' via as \<equiv> 
    (\<exists>a a' as'. (as = a#as') \<and> (n' \<notin> set(sourcenodes as)) \<and> (n -as\<rightarrow>* n') \<and>
                   (sourcenode a = n) \<and> (n' strongly-postdominates (targetnode a)) \<and>
                   (valid_edge a') \<and> (sourcenode a' = n) \<and> 
                   (\<not> n' strongly-postdominates (targetnode a')))"


lemma (in StrongPostdomination) Exit_not_dyn_weak_control_dependent:
  assumes control:"n weakly controls (_Exit_) via as" shows "False"
proof -
  from control obtain as a as' where path:"n -as\<rightarrow>* (_Exit_)" and as:"as = a#as'"
    and pd:"(_Exit_) postdominates (targetnode a)"
    by(auto simp:dyn_weak_control_dependence_def strong_postdominate_def)
  from path as have "n -[]@a#as'\<rightarrow>* (_Exit_)" by simp
  hence "targetnode a -as'\<rightarrow>* (_Exit_)" by(fastsimp dest:path_split)
  with pd show False by -(erule Exit_no_postdominator)
qed

subsubsection {* Instantiate dynamic PDG *}

locale DynWeakControlDependencePDG = StrongPostdomination + CFGExit_wf

begin

lemma DynPDG_wcd:
  "DynPDG sourcenode targetnode kind valid_edge (_Entry_) 
          Def Use state_val (_Exit_) dyn_weak_control_dependence"
proof(unfold_locales)
  fix n n' as assume "n weakly controls n' via as"
  show "n' \<noteq> (_Exit_)"
  proof(rule ccontr)
    assume "\<not> n' \<noteq> (_Exit_)"
    hence "n' = (_Exit_)" by simp
    with `n weakly controls n' via as` show False
      by(fastsimp intro:Exit_not_dyn_weak_control_dependent)
  qed
next
  fix n n' as assume "n weakly controls n' via as"
  thus "n -as\<rightarrow>* n' \<and> as \<noteq> []"
    by(fastsimp simp:dyn_weak_control_dependence_def)
qed


end


subsection {* Static weak control dependence *}

subsubsection {* Definition and some lemmas *}

definition (in StrongPostdomination) 
  weak_control_dependence :: "'node \<Rightarrow> 'node \<Rightarrow> bool" 
  ("_ weakly controls _" [51,0])
where weak_control_dependences_eq:
    "n weakly controls n' \<equiv> \<exists>as. n weakly controls n' via as"

lemma (in StrongPostdomination) 
  weak_control_dependence_def:"n weakly controls n' = 
    (\<exists>as a a' as'. (as = a#as') \<and> (n' \<notin> set(sourcenodes as)) \<and> (n -as\<rightarrow>* n') \<and>
                   (sourcenode a = n) \<and> (n' strongly-postdominates (targetnode a)) \<and>
                   (valid_edge a') \<and> (sourcenode a' = n) \<and> 
                   (\<not> n' strongly-postdominates (targetnode a')))"
by(auto simp:weak_control_dependences_eq dyn_weak_control_dependence_def)


lemma (in StrongPostdomination) Exit_not_weak_control_dependent:
  "n weakly controls (_Exit_) \<Longrightarrow> False"
by(auto simp:weak_control_dependences_eq 
        intro:Exit_not_dyn_weak_control_dependent)


subsubsection {* Instantiate static PDG *}

locale WeakControlDependencePDG = StrongPostdomination + CFGExit_wf

begin

lemma PDG_wcd:
  "PDG sourcenode targetnode kind valid_edge (_Entry_) 
       Def Use state_val (_Exit_) weak_control_dependence"
proof(unfold_locales)
  fix n n' assume "n weakly controls n'"
  show "n' \<noteq> (_Exit_)"
  proof(rule ccontr)
    assume "\<not> n' \<noteq> (_Exit_)"
    hence "n' = (_Exit_)" by simp
    with `n weakly controls n'` show False
      by(fastsimp intro:Exit_not_weak_control_dependent)
  qed
next
  fix n n' assume "n weakly controls n'"
  thus "\<exists>as. n -as\<rightarrow>* n' \<and> as \<noteq> []"
    by(fastsimp simp:weak_control_dependence_def)
qed

(*<*)
lemmas PDG_cdep_edge = PDG.PDG_cdep_edge[OF PDG_wcd]
lemmas PDG_path_Nil = PDG.PDG_path_Nil[OF PDG_wcd]
lemmas PDG_path_Append = PDG.PDG_path_Append[OF PDG_wcd]
lemmas PDG_path_CFG_path = PDG.PDG_path_CFG_path[OF PDG_wcd]
lemmas PDG_path_cdep = PDG.PDG_path_cdep[OF PDG_wcd]
lemmas PDG_path_ddep = PDG.PDG_path_ddep[OF PDG_wcd]
lemmas PDG_path_not_inner = PDG.PDG_path_not_inner[OF PDG_wcd]
lemmas PDG_path_Exit = PDG.PDG_path_Exit[OF PDG_wcd]


definition PDG_BS_w :: "'b \<Rightarrow> 'b set" ("PDG'_BS")
  where "PDG_BS n \<equiv> 
  PDG.PDG_BS sourcenode targetnode valid_edge Def Use weak_control_dependence n"

lemma [simp]: "PDG.PDG_BS sourcenode targetnode valid_edge Def Use 
  weak_control_dependence n = PDG_BS n"
  by(simp add:PDG_BS_w_def)

lemmas PDG_BS_def = PDG.PDG_BS_def[OF PDG_wcd,simplified]
lemmas PDG_BS_valid_node = PDG.PDG_BS_valid_node[OF PDG_wcd,simplified]
lemmas Exit_PDG_BS = PDG.Exit_PDG_BS[OF PDG_wcd,simplified]
(*>*)

end

end