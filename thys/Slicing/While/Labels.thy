section {* Labels *}

theory Labels imports Com begin

text {* Labels describe a mapping from the inner node label 
  to the matching command *}

inductive labels :: "cmd \<Rightarrow> nat \<Rightarrow> cmd \<Rightarrow> bool"
where

Labels_Base:
  "labels c 0 c"

| Labels_LAss:
  "labels (V:=e) 1 Skip"

| Labels_Seq1: 
  "labels c\<^sub>1 l c \<Longrightarrow> labels (c\<^sub>1;;c\<^sub>2) l (c;;c\<^sub>2)"

| Labels_Seq2: 
  "labels c\<^sub>2 l c \<Longrightarrow> labels (c\<^sub>1;;c\<^sub>2) (l + #:c\<^sub>1) c"

| Labels_CondTrue:
  "labels c\<^sub>1 l c \<Longrightarrow> labels (if (b) c\<^sub>1 else c\<^sub>2) (l + 1) c"

| Labels_CondFalse:
  "labels c\<^sub>2 l c \<Longrightarrow> labels (if (b) c\<^sub>1 else c\<^sub>2) (l + #:c\<^sub>1 + 1) c"

| Labels_WhileBody:
  "labels c' l c \<Longrightarrow> labels (while(b) c') (l + 2) (c;;while(b) c')"

| Labels_WhileExit:
  "labels (while(b) c') 1 Skip"

lemma label_less_num_inner_nodes:
  "labels c l c' \<Longrightarrow> l < #:c"
proof(induct c arbitrary:l c')
  case Skip 
  from `labels Skip l c'` show ?case by(fastforce elim:labels.cases)
next
  case (LAss V e) 
  from `labels (V:=e) l c'` show ?case by(fastforce elim:labels.cases)
next
  case (Seq c\<^sub>1 c\<^sub>2)
  note IH1 = `\<And>l c'. labels c\<^sub>1 l c' \<Longrightarrow> l < #:c\<^sub>1`
  note IH2 = `\<And>l c'. labels c\<^sub>2 l c' \<Longrightarrow> l < #:c\<^sub>2`
  from `labels (c\<^sub>1;;c\<^sub>2) l c'` IH1 IH2 show ?case
    by simp(erule labels.cases,auto,force)
next
  case (Cond b c\<^sub>1 c\<^sub>2)
  note IH1 = `\<And>l c'. labels c\<^sub>1 l c' \<Longrightarrow> l < #:c\<^sub>1`
  note IH2 = `\<And>l c'. labels c\<^sub>2 l c' \<Longrightarrow> l < #:c\<^sub>2`
  from `labels (if (b) c\<^sub>1 else c\<^sub>2) l c'` IH1 IH2 show ?case
    by simp(erule labels.cases,auto,force)
next
  case (While b c)
  note IH = `\<And>l c'. labels c l c' \<Longrightarrow> l < #:c`
  from `labels (while (b) c) l c'` IH show ?case
    by simp(erule labels.cases,fastforce+)
qed


declare One_nat_def [simp del]

lemma less_num_inner_nodes_label:
  "l < #:c \<Longrightarrow> \<exists>c'. labels c l c'"
proof(induct c arbitrary:l)
  case Skip
  from `l < #:Skip` have "l = 0" by simp
  thus ?case by(fastforce intro:Labels_Base)
next
  case (LAss V e)
  from `l < #:(V:=e)` have "l = 0 \<or> l = 1" by auto
  thus ?case by(auto intro:Labels_Base Labels_LAss)
next
  case (Seq c\<^sub>1 c\<^sub>2)
  note IH1 = `\<And>l. l < #:c\<^sub>1 \<Longrightarrow> \<exists>c'. labels c\<^sub>1 l c'`
  note IH2 = `\<And>l. l < #:c\<^sub>2 \<Longrightarrow> \<exists>c'. labels c\<^sub>2 l c'`
  show ?case
  proof(cases "l < #:c\<^sub>1")
    case True
    from IH1[OF this] obtain c' where "labels c\<^sub>1 l c'" by auto
    hence "labels (c\<^sub>1;;c\<^sub>2) l (c';;c\<^sub>2)" by(fastforce intro:Labels_Seq1)
    thus ?thesis by auto
  next
    case False
    hence "#:c\<^sub>1 \<le> l" by simp
    then obtain l' where "l = l' + #:c\<^sub>1" and "l' = l - #:c\<^sub>1" by simp
    from `l = l' + #:c\<^sub>1` `l < #:c\<^sub>1;;c\<^sub>2` have "l' < #:c\<^sub>2" by simp
    from IH2[OF this] obtain c' where "labels c\<^sub>2 l' c'" by auto
    with `l = l' + #:c\<^sub>1` have "labels (c\<^sub>1;;c\<^sub>2) l c'" by(fastforce intro:Labels_Seq2)
    thus ?thesis by auto
  qed
next
  case (Cond b c\<^sub>1 c\<^sub>2)
  note IH1 = `\<And>l. l < #:c\<^sub>1 \<Longrightarrow> \<exists>c'. labels c\<^sub>1 l c'`
  note IH2 = `\<And>l. l < #:c\<^sub>2 \<Longrightarrow> \<exists>c'. labels c\<^sub>2 l c'`
  show ?case
  proof(cases "l = 0")
    case True
    thus ?thesis by(fastforce intro:Labels_Base)
  next
    case False
    hence "0 < l" by simp
    then obtain l' where "l = l' + 1" and "l' = l - 1" by simp
    thus ?thesis
    proof(cases "l' < #:c\<^sub>1")
      case True
      from IH1[OF this] obtain c' where "labels c\<^sub>1 l' c'" by auto
      with `l = l' + 1` have "labels (if (b) c\<^sub>1 else c\<^sub>2) l c'"
        by(fastforce dest:Labels_CondTrue)
      thus ?thesis by auto
    next
      case False
      hence "#:c\<^sub>1 \<le> l'" by simp
      then obtain l'' where "l' = l'' + #:c\<^sub>1" and "l'' = l' - #:c\<^sub>1" by simp
      from `l' = l'' + #:c\<^sub>1` `l = l' + 1` `l < #:if (b) c\<^sub>1 else c\<^sub>2`
      have "l'' < #:c\<^sub>2" by simp
      from IH2[OF this] obtain c' where "labels c\<^sub>2 l'' c'" by auto
      with `l' = l'' + #:c\<^sub>1` `l = l' + 1` have "labels (if (b) c\<^sub>1 else c\<^sub>2) l c'"
        by(fastforce dest:Labels_CondFalse)
      thus ?thesis by auto
    qed
  qed
next
  case (While b c')
  note IH = `\<And>l. l < #:c' \<Longrightarrow> \<exists>c''. labels c' l c''`
  show ?case
  proof(cases "l < 1")
    case True
    hence "l = 0" by simp
    thus ?thesis by(fastforce intro:Labels_Base)
  next
    case False
    show ?thesis
    proof(cases "l < 2")
      case True
      with `\<not> l < 1` have "l = 1" by simp
      thus ?thesis by(fastforce intro:Labels_WhileExit)
    next
      case False
      with `\<not> l < 1` have "2 \<le> l" by simp
      then obtain l' where "l = l' + 2" and "l' = l - 2" 
        by(simp del:add_2_eq_Suc')
      from `l = l' + 2` `l < #:while (b) c'` have "l' < #:c'" by simp
      from IH[OF this] obtain c'' where "labels c' l' c''" by auto
      with `l = l' + 2` have "labels (while (b) c') l (c'';;while (b) c')"
        by(fastforce dest:Labels_WhileBody)
      thus ?thesis by auto
    qed
  qed
qed



lemma labels_det:
  "labels c l c'\<Longrightarrow> (\<And>c''. labels c l c''\<Longrightarrow> c' = c'')"
proof(induct rule: labels.induct)
  case (Labels_Base c c'') 
  from `labels c 0 c''` obtain l where "labels c l c''" and "l = 0" by auto
  thus ?case by(induct rule: labels.induct,auto)
next
  case (Labels_Seq1 c\<^sub>1 l c c\<^sub>2)
  note IH = `\<And>c''. labels c\<^sub>1 l c'' \<Longrightarrow> c = c''`
  from `labels c\<^sub>1 l c` have "l < #:c\<^sub>1" by(fastforce intro:label_less_num_inner_nodes)
  with `labels (c\<^sub>1;;c\<^sub>2) l c''` obtain cx where "c'' = cx;;c\<^sub>2 \<and> labels c\<^sub>1 l cx"
    by(fastforce elim:labels.cases intro:Labels_Base)
  hence [simp]:"c'' = cx;;c\<^sub>2" and "labels c\<^sub>1 l cx" by simp_all
  from IH[OF `labels c\<^sub>1 l cx`] show ?case by simp
next
  case (Labels_Seq2 c\<^sub>2 l c c\<^sub>1)
  note IH = `\<And>c''. labels c\<^sub>2 l c'' \<Longrightarrow> c = c''`
  from `labels (c\<^sub>1;;c\<^sub>2) (l + #:c\<^sub>1) c''` `labels c\<^sub>2 l c` have "labels c\<^sub>2 l c''" 
    by(auto elim:labels.cases dest:label_less_num_inner_nodes)
  from IH[OF this] show ?case .
next
  case (Labels_CondTrue c\<^sub>1 l c b c\<^sub>2)
  note IH = `\<And>c''. labels c\<^sub>1 l c'' \<Longrightarrow>  c = c''`
  from `labels (if (b) c\<^sub>1 else c\<^sub>2) (l + 1) c''` `labels c\<^sub>1 l c` have "labels c\<^sub>1 l c''"
    by(fastforce elim:labels.cases dest:label_less_num_inner_nodes)
  from IH[OF this] show ?case .
next
  case (Labels_CondFalse c\<^sub>2 l c b c\<^sub>1)
  note IH = `\<And>c''. labels c\<^sub>2 l c'' \<Longrightarrow>  c = c''`
  from `labels (if (b) c\<^sub>1 else c\<^sub>2) (l + #:c\<^sub>1 + 1) c''` `labels c\<^sub>2 l c`
  have "labels c\<^sub>2 l c''"
    by(fastforce elim:labels.cases dest:label_less_num_inner_nodes)
  from IH[OF this] show ?case .
next
  case (Labels_WhileBody c' l c b)
  note IH = `\<And>c''. labels c' l c'' \<Longrightarrow> c = c''`
  from `labels (while (b) c') (l + 2) c''` `labels c' l c` 
  obtain cx where "c'' = cx;;while (b) c' \<and> labels c' l cx" 
    by -(erule labels.cases,auto)
  hence [simp]:"c'' = cx;;while (b) c'" and "labels c' l cx" by simp_all
  from IH[OF `labels c' l cx`] show ?case by simp
qed (fastforce elim:labels.cases)+


end
