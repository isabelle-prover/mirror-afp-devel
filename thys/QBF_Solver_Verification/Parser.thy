section \<open>QDIMACS Parser\<close>

theory Parser
  imports PCNF
begin

type_synonym 'a parser = "string \<Rightarrow> ('a \<times> string) option"

fun trim_ws :: "string \<Rightarrow> string" where
  "trim_ws Nil = Nil"
| "trim_ws (Cons x xs) = (if x = CHR '' '' then trim_ws xs else Cons x xs)"

lemma non_increasing_trim_ws [simp]: "length (trim_ws s) \<le> length s"
  by (induction s) auto

lemma non_increasing_trim_ws_lemmas [intro]:
  shows "length s \<le> length s' \<Longrightarrow> length (trim_ws s) \<le> length s'"
    and "length s < length s' \<Longrightarrow> length (trim_ws s) < length s'"
    and "length s \<le> length (trim_ws s') \<Longrightarrow> length s \<le> length s'"
    and "length s < length (trim_ws s') \<Longrightarrow> length s < length s'"
     apply (induction s)
         apply simp_all
  subgoal using trim_ws.simps(1) by blast
  subgoal using non_increasing_trim_ws order_less_le_trans by blast
  done

lemma whitespace_and_parse_le [intro]:
  assumes "\<And>s s' r. p s = Some (r, s') \<Longrightarrow> length s' \<le> length s"
  shows "\<And>s s' r. p (trim_ws s) = Some (r, s') \<Longrightarrow> length s' \<le> length s" using assms
  using le_trans non_increasing_trim_ws by blast

lemma whitespace_and_parse_unit_le [intro]:
  assumes "\<And>s s'. p s = Some ((), s') \<Longrightarrow> length s' \<le> length s"
  shows "\<And>s s'. p (trim_ws s) = Some ((), s') \<Longrightarrow> length s' \<le> length s" using assms
  using le_trans non_increasing_trim_ws by blast

lemma whitespace_and_parse_less [intro]:
  assumes "\<And>s s' r. p s = Some (r, s') \<Longrightarrow> length s' < length s"
  shows "\<And>s s' r. p (trim_ws s) = Some (r, s') \<Longrightarrow> length s' < length s" using assms
  using non_increasing_trim_ws order_less_le_trans by blast

lemma whitespace_and_parse_unit_less [intro]:
  assumes "\<And>s s'. p s = Some ((), s') \<Longrightarrow> length s' < length s"
  shows "\<And>s s'. p (trim_ws s) = Some ((), s') \<Longrightarrow> length s' < length s" using assms
  using non_increasing_trim_ws order_less_le_trans by blast

fun match :: "string \<Rightarrow> unit parser" where
  "match Nil str = Some ((), str)"
| "match (Cons x xs) Nil = None"
| "match (Cons x xs) (Cons y ys) = (if x \<noteq> y then None else match xs ys)"

lemma non_increasing_match [simp]: "match xs s = Some ((), s') \<Longrightarrow> length s' \<le> length s"
  apply (induction xs s rule: match.induct)
    apply auto[2]
  by (metis le_imp_less_Suc length_Cons match.simps(3) option.simps(3) order_less_imp_le)

lemma decreasing_match [simp]:
  "xs \<noteq> [] \<Longrightarrow> match xs s = Some ((), s') \<Longrightarrow> length s' < length s"
proof (induction xs s rule: match.induct)
  case (3 x xs y ys)
  hence "x = y" by (cases "x = y") auto
  hence "match (Cons x xs) (Cons y ys) = match xs ys" by simp
  hence "match xs ys = Some ((), s')" using 3 by simp
  hence "length s' \<le> length ys" by simp
  thus "length s' < length (Cons y ys)" by simp
qed auto

fun digit_to_nat :: "char \<Rightarrow> nat option" where
  "digit_to_nat c = (
    if c = CHR ''0'' then Some 0 else
    if c = CHR ''1'' then Some 1 else
    if c = CHR ''2'' then Some 2 else
    if c = CHR ''3'' then Some 3 else
    if c = CHR ''4'' then Some 4 else
    if c = CHR ''5'' then Some 5 else
    if c = CHR ''6'' then Some 6 else
    if c = CHR ''7'' then Some 7 else
    if c = CHR ''8'' then Some 8 else
    if c = CHR ''9'' then Some 9 else
    None)"

fun num_aux :: "nat \<Rightarrow> nat parser" where
  "num_aux n Nil = Some (n, Nil)"
| "num_aux n (Cons x xs) =
     (if List.member ''0123456789'' x
        then num_aux (10 * n + the (digit_to_nat x)) xs
        else Some (n, Cons x xs))"

lemma non_increasing_num_aux [simp]: "num_aux n s = Some (m, s') \<Longrightarrow> length s' \<le> length s"
  apply (induction n s rule: num_aux.induct)
   apply simp
  by (metis (no_types, lifting) le_imp_less_Suc length_Cons nle_le num_aux.simps(2) option.sel order_less_imp_le prod.sel(2))

fun pnum_raw :: "nat parser" where
  "pnum_raw Nil = None"
| "pnum_raw (Cons x xs) = (if List.member ''0123456789'' x then num_aux 0 (Cons x xs) else None)"

lemma decreasing_pnum_raw [simp]: "pnum_raw s = Some (n, s') \<Longrightarrow> length s' < length s"
  apply (cases s)
   apply simp
  apply (metis impossible_Cons nat_less_le non_increasing_num_aux num_aux.simps(2) option.simps(3) pnum_raw.simps(2))
  done

(* Parse pnum *)
fun pnum :: "nat parser" where
  "pnum str = (case pnum_raw str of
    None \<Rightarrow> None |
    Some (n, str') \<Rightarrow> if n = 0 then None else Some (n, str'))"

text \<open>Simple tests.\<close>

value "pnum ''123''"
value "pnum ''-123''"
value "pnum ''0123''"
value "pnum ''0''"

lemma decreasing_pnum [simp]:
  assumes "pnum s = Some (n, s')"
  shows "length s' < length s"
proof (cases "pnum_raw s")
  case None
  hence False using assms by simp
  thus ?thesis by simp
next
  case (Some a)
  obtain n' s'' where "a = (n', s'')" by fastforce
  then show ?thesis using Some assms by (cases "n' = 0") auto
qed

(* Parse <literal> ::= <num>; no whitespace *)
fun literal :: "PCNF.literal parser" where
  "literal str = (case match ''-'' str of
    None \<Rightarrow> (case pnum str of
      None \<Rightarrow> None |
      Some (n, str') \<Rightarrow> Some (P n, str')) |
    Some (_, str') \<Rightarrow> (case pnum str' of
      None \<Rightarrow> None |
      Some (n, str'') \<Rightarrow> Some (N n, str'')))"

text \<open>Simple tests.\<close>

value "literal ''123''"
value "literal ''-123''"
value "literal ''- 123''"
value "literal ''0123''"
value "literal ''0''"

lemma decreasing_literal [simp]:
  assumes "literal s = Some (l, s')"
  shows "length s' < length s"
proof (cases "match ''-'' s")
  case None
  thus ?thesis using assms by (cases "pnum s") auto
next
  case (Some a)
  from this obtain s'' where s''_def: "a = ((), s'')" by (cases "match ''-'' s") auto
  hence "length s'' \<le> length s" using Some by simp
  moreover have "length s' < length s''" using s''_def assms Some by (cases "pnum s''") auto
  ultimately show "length s' < length s" by simp
qed

(* Parse <clause> ::= <literal> <clause> | <literal> 0 EOL; whitespace allowed *)
fun clause :: "PCNF.clause parser" where
"clause str = (case literal (trim_ws str) of
  None \<Rightarrow> None |
  Some (l, str') \<Rightarrow>
    (case clause str' of
      None \<Rightarrow>
        (case match ''0'' (trim_ws str') of
          None \<Rightarrow> None |
          Some (_, str'') \<Rightarrow>
            (case match ''\<newline>'' (trim_ws str'') of
              None \<Rightarrow> None |
              Some (_, str''') \<Rightarrow> Some (Cons l Nil, str'''))) |
      Some (cl, str'') \<Rightarrow> Some (Cons l cl, str'')))"

text \<open>Simple tests.\<close>

value "clause ''1 2 -3 4 0 \<newline>''"
value "clause ''1 2 -3   4   0 \<newline>''"
value "clause ''1 2 -3 40 \<newline>''"
value "clause ''1 2 -3 4 0\<newline>''"
value "clause ''1 2 -3 4 0''"
value "clause '' 1 2 -3 4 0 \<newline>''"

lemma decreasing_clause [simp]:
  assumes "clause s = Some (c, s')"
  shows "length s' < length s" using assms
proof (induction s arbitrary: c rule: clause.induct)
  case (1 s)
  show ?case
  proof (cases "literal (trim_ws s)")
    case None
    hence False using 1 by simp
    thus ?thesis by simp
  next
    case Some_a: (Some a)
    obtain l s'' where a_def: "a = (l, s'')" by fastforce
    hence less1: "length s'' < length s" using Some_a by fastforce
    show ?thesis
    proof (cases "clause s''")
      case None': None
      show ?thesis
      proof (cases "match ''0'' (trim_ws s'')")
        case None
        hence False using 1 Some_a a_def None' by simp
        thus ?thesis by simp
      next
        case Some_b: (Some b)
        obtain u s''' where b_def: "b = (u, s''')" by (meson surj_pair)
        hence le1: "length s''' \<le> length s''" using Some_b by fastforce
        show ?thesis
        proof (cases "match ''\<newline>'' (trim_ws s''')")
          case None
          hence False using 1 Some_a a_def None' Some_b b_def by simp
          thus ?thesis by simp
        next
          case Some_c: (Some c)
          obtain u s'''' where c_def: "c = (u, s'''')" by (meson surj_pair)
          hence le2: "length s'''' \<le> length s'''" using Some_c by fastforce
          have "clause s = Some (Cons l Nil, s'''')"
            using Some_a a_def None' Some_b b_def Some_c c_def by simp
          hence "s'''' = s'" using 1(2) by simp
          thus "length s' < length s" using less1 le1 le2 by simp
        qed
      qed
    next
      case Some_b: (Some b)
      obtain c' s''' where b_def: "b = (c', s''')" by fastforce
      hence "clause s = Some (Cons l c', s''')" using Some_a Some_b a_def by simp
      hence "s''' = s'" using 1(2) by simp
      hence "clause s'' = Some (c', s')" using Some_b b_def by simp
      hence "length s' < length s''" using 1(1) Some_a a_def by blast
      thus "length s' < length s" using less1 by simp
    qed
  qed
qed

(* Parse <clause_list> ::= <clause> <clause_list> | <clause>; no whitespace*)
fun clause_list :: "PCNF.matrix parser" where
  "clause_list str = (case clause str of
    None \<Rightarrow> None |
    Some (cl, str') \<Rightarrow>
      (case clause_list str' of
        None \<Rightarrow> Some (Cons cl Nil, str') |
        Some (cls, str'') \<Rightarrow> Some (Cons cl cls, str'')))"

text \<open>Simple tests.\<close>

value "clause_list ''1 2 -3 0\<newline>1 -2 3 0\<newline>-1 2  3 0\<newline>''"
value "clause_list ''1 2 -3 \<newline>1 -2 3 0\<newline>-1 2  3 0\<newline>''"
value "clause_list ''1 2 -3 0 \<newline> 1 -2 3 0\<newline>-1 2  3 0\<newline>''"

lemma decreasing_clause_list [simp]:
  assumes "clause_list s = Some (cls, s')"
  shows "length s' < length s" using assms
proof (induction s arbitrary: cls rule: clause_list.induct)
  case (1 s)
  show ?case
  proof (cases "clause s")
    case None
    hence False using 1 by simp
    thus ?thesis by simp
  next
    case Some_a: (Some a)
    obtain cl s'' where a_def: "a = (cl, s'')" by fastforce
    hence less1: "length s'' < length s" using Some_a by simp
    show ?thesis
    proof (cases "clause_list s''")
      case None
      hence "clause_list s = Some (Cons cl Nil, s'')" using Some_a a_def by simp
      hence "s' = s''" using 1 by simp
      thus "length s' < length s" using less1 by simp
    next
      case Some_b: (Some b)
      obtain cls s''' where b_def: "b = (cls, s''')" by fastforce
      hence "clause_list s = Some (Cons cl cls, s''')" using Some_b Some_a a_def by simp
      hence "s' = s'''" using 1 by simp
      hence "clause_list s'' = Some (cls, s')" using Some_b b_def by simp
      hence "length s' < length s''" using 1 Some_a a_def by blast
      thus ?thesis using less1 by simp
    qed
  qed
qed

(* Parse <matrix> ::= <clause_list>; no whitespace *)
fun matrix :: "PCNF.matrix parser" where
  "matrix s = clause_list s"

text \<open>Simple tests.\<close>

value "matrix ''1 2 -3 0\<newline>1 -2 3 0\<newline>-1 2  3 0\<newline>''"
value "matrix ''1 2 -3 \<newline>1 -2 3 0\<newline>-1 2  3 0\<newline>''"
value "matrix ''1 2 -3 0 \<newline> 1 -2 3 0\<newline>-1 2  3 0\<newline>''"

lemma decreasing_matrix [simp]: "matrix s = Some (mat, s') \<Longrightarrow> length s' < length s" by simp

(* Parse <atom_set> ::= <pnum> <atom_set> | <pnum>; whitespace allowed *)
fun atom_set :: "(nat \<times> nat list) parser" where
  "atom_set str = (case pnum (trim_ws str) of
    None \<Rightarrow> None |
    Some (a, str') \<Rightarrow>
      (case atom_set str' of
        None \<Rightarrow> Some ((a, Nil), str') |
        Some ((a', as), str'') \<Rightarrow> Some ((a, Cons a' as), str'')))"

text \<open>Simple tests.\<close>

value "atom_set ''1 2 3 4''"
value "atom_set ''1 2 -3 4''"
value "atom_set ''1 2 3   4   0 \<newline>''"
value "atom_set ''1 2 3 40''"
value "atom_set ''1 2 3 4 0\<newline>''"
value "atom_set ''1 2 3 4''"
value "atom_set '' 1   2  3 4 0 \<newline>  ''"

lemma decreasing_atom_set [simp]:
  assumes "atom_set s = Some (as, s')"
  shows "length s' < length s" using assms
proof (induction s arbitrary: as rule: atom_set.induct)
  case (1 s)
  show ?case
  proof (cases "pnum (trim_ws s)")
    case None
    hence False using 1 by simp
    thus ?thesis by simp
  next
    case Some_b: (Some b)
    obtain a s'' where b_def: "b = (a, s'')" by fastforce
    hence less1: "length s'' < length s" using Some_b by fastforce
    show ?thesis
    proof (cases "atom_set s''")
      case None
      hence "atom_set s = Some ((a, Nil), s'')" using Some_b b_def by simp
      hence "s' = s''" using 1 by simp
      thus "length s' < length s" using less1 by simp
    next
      case Some_c: (Some c)
      obtain a_set s''' where "c = (a_set, s''')" by fastforce
      moreover obtain a' as where "a_set = (a', as)" by fastforce
      ultimately have c_def: "c = ((a', as), s''')" by simp
      hence "atom_set s = Some ((a, Cons a' as), s''')" using Some_c Some_b b_def by simp
      hence "s' = s'''" using 1 by simp
      hence "atom_set s'' = Some ((a', as), s')" using Some_c c_def by simp
      hence "length s' < length s''" using 1 Some_b b_def by blast
      thus "length s' < length s" using less1 by simp
    qed
  qed
qed

(* Parse <quantifier> ::= e | a; no whitespace *)
datatype quant = Universal | Existential

fun quantifier :: "quant parser" where
  "quantifier str = (case match ''e'' str of
    None \<Rightarrow> (case match ''a'' str of
      None \<Rightarrow> None |
      Some (_, str') \<Rightarrow> Some (Universal, str')) |
    Some (_, str') \<Rightarrow> Some (Existential, str'))"

text \<open>Simple tests.\<close>

value "quantifier ''a 1 2 3''"
value "quantifier ''e 1 2 3''"
value "quantifier ''a 1 2 3''"
value "quantifier '' e 1 2 3''"

lemma non_increasing_quant [simp]:
  assumes "quantifier s = Some (q, s')"
  shows "length s' \<le> length s"
proof (cases "match ''e'' s")
  case None_e: None
  then show ?thesis
  proof (cases "match ''a'' s")
    case None
    hence False using None_e assms by simp
    thus ?thesis by simp
  next
    case Some_a: (Some a)
    obtain u s'' where a_def: "a = (u, s'')" by (meson surj_pair)
    hence "quantifier s = Some (Universal, s'')" using None_e Some_a by simp
    hence "s' = s''" using assms by simp
    thus "length s' \<le> length s" using Some_a a_def by simp
  qed
next
  case Some_a: (Some a)
  obtain u s'' where a_def: "a = (u, s'')" by (meson surj_pair)
  hence "quantifier s = Some (Existential, s'')" using Some_a by simp
  hence "s' = s''" using assms by simp
  thus "length s' \<le> length s" using Some_a a_def by simp
qed

(* Parse <quant_set> ::= <quantifier> <atom_set> 0 EOL; whitespace allowed *)
fun quant_set :: "(quant \<times> (nat \<times> nat list)) parser" where
  "quant_set str = (case quantifier (trim_ws str) of
    None \<Rightarrow> None |
    Some (q, str') \<Rightarrow>
      (case atom_set (trim_ws str') of
        None \<Rightarrow> None |
        Some (as, str'') \<Rightarrow>
          (case match ''0'' (trim_ws str'') of
            None \<Rightarrow> None |
            Some (_, str''') \<Rightarrow>
              (case match ''\<newline>'' (trim_ws str''') of
                None \<Rightarrow> None |
                Some (_, str'''') \<Rightarrow> Some ((q, as), str'''')))))"

text \<open>Simple tests.\<close>

value "quant_set ''e 1 2  3 0\<newline>''"
value "quant_set ''a 1 2 3 0\<newline>''"
value "quant_set ''a 1 2 -3 0\<newline>''"

lemma decreasing_quant_set [simp]:
  assumes "quant_set s = Some (q_set, s')"
  shows "length s' < length s"
proof (cases "quantifier (trim_ws s)")
  case None
  hence False using assms by simp
  thus ?thesis by simp
next
  case Some_a: (Some a)
  obtain q s'' where a_def: "a = (q, s'')" by fastforce
  hence le1: "length s'' \<le> length s" using Some_a by fastforce
  show ?thesis
  proof (cases "atom_set (trim_ws s'')")
    case None
    hence False using Some_a a_def assms by simp
    thus ?thesis by simp
  next
    case Some_b: (Some b)
    obtain as s''' where b_def: "b = (as, s''')" by fastforce
    hence less1: "length s''' < length s''" using Some_b by fastforce
    show ?thesis
    proof (cases "match ''0'' (trim_ws s''')")
      case None
      hence False using Some_a a_def Some_b b_def assms by simp
      thus ?thesis by simp
    next
      case Some_c: (Some c)
      obtain u s'''' where c_def: "c = (u, s'''')" by (meson surj_pair)
      hence le2: "length s'''' \<le> length s'''" using Some_c by fastforce
      show ?thesis
      proof (cases "match ''\<newline>'' (trim_ws s'''')")
        case None
        hence False using Some_a a_def Some_b b_def Some_c c_def assms by simp
        thus ?thesis by simp
      next
        case Some_d: (Some d)
        obtain u s''''' where d_def: "d = (u, s''''')" by (meson surj_pair)
        hence le3: "length s''''' \<le> length s''''" using Some_d by fastforce
        have "quant_set s = Some ((q, as), s''''')"
          using Some_a a_def Some_b b_def Some_c c_def Some_d d_def by simp
        hence "s' = s'''''" using assms by simp
        thus "length s' < length s" using less1 le1 le2 le3 by simp
      qed
    qed
  qed
qed

(* Parse <quant_sets> ::= <quant_set> <quant_sets> | <quant_set>; no whitespace *)
fun quant_sets :: "(quant \<times> (nat \<times> nat list)) list parser" where
  "quant_sets str = (case quant_set str of
    None \<Rightarrow> None |
    Some (q_set, str') \<Rightarrow>
      (case quant_sets str' of
        None \<Rightarrow> Some (Cons q_set Nil, str') |
        Some (q_sets, str'') \<Rightarrow> Some (Cons q_set q_sets, str'')))"

text \<open>Simple tests.\<close>

value "quant_sets ''a 1 2 3 0\<newline>e 4 5 6 0\<newline>a 7 8  9 0 \<newline>''"
value "quant_sets ''a 1 2 3 0\<newline>  e  4  5  6  0 \<newline>e 7 8  9 0 \<newline>''"

lemma decreasing_quant_sets [simp]:
  assumes "quant_sets s = Some (q_sets, s')"
  shows "length s' < length s" using assms
proof (induction s arbitrary: q_sets rule: quant_sets.induct)
  case (1 s)
  show ?case
  proof (cases "quant_set s")
    case None
    hence False using 1 by simp
    thus ?thesis by simp
  next
    case Some_a: (Some a)
    obtain q_set s'' where a_def: "a = (q_set, s'')" by fastforce
    hence less1: "length s'' < length s" using Some_a by simp
    show ?thesis
    proof (cases "quant_sets s''")
      case None
      hence "quant_sets s = Some (Cons q_set Nil, s'')" using Some_a a_def by simp
      hence "s' = s''" using 1 by simp
      thus "length s' < length s" using less1 by simp
    next
      case Some_b: (Some b)
      obtain q_sets s''' where b_def: "b = (q_sets, s''')" by fastforce
      hence "quant_sets s = Some (Cons q_set q_sets, s''')" using Some_a a_def Some_b by simp
      hence "s' = s'''" using 1 by simp
      hence "quant_sets s'' = Some (q_sets, s')" using Some_b b_def by simp
      hence "length s' < length s''" using 1 Some_a a_def by simp
      thus "length s' < length s" using less1 by simp
    qed
  qed
qed

fun convert_quant_sets :: "(quant \<times> (nat \<times> nat list)) list \<Rightarrow> PCNF.prefix option" where
  "convert_quant_sets Nil = Some Empty"
| "convert_quant_sets (Cons (Universal, as) qs) =
    (case convert_quant_sets qs of
      None \<Rightarrow> None |
      Some Empty \<Rightarrow> Some (UniversalFirst as Nil) |
      Some (ExistentialFirst as' qs') \<Rightarrow> Some (UniversalFirst as (Cons as' qs')) |
      Some (UniversalFirst _ _) \<Rightarrow> None)"
| "convert_quant_sets (Cons (Existential, as) qs) =
    (case convert_quant_sets qs of
      None \<Rightarrow> None |
      Some Empty \<Rightarrow> Some (ExistentialFirst as Nil) |
      Some (ExistentialFirst _ _) \<Rightarrow> None |
      Some (UniversalFirst as' qs') \<Rightarrow> Some (ExistentialFirst as (Cons as' qs')))"

(* Parser <prefix> ::= [<quant_sets>]; no whitespace *)
fun prefix :: "PCNF.prefix parser" where
  "prefix str = (case quant_sets str of
    None \<Rightarrow> Some (Empty, str) |
    Some (pre, str') \<Rightarrow>
      (case convert_quant_sets pre of
        None \<Rightarrow> None |
        Some converted \<Rightarrow> Some (converted, str')))"

text \<open>Simple tests.\<close>

value "prefix ''a 1 2 3 0\<newline>e 4 5 6 0\<newline>a 7 8  9 0 \<newline>''"
value "prefix ''a 1 2 3 0\<newline>e 4 5 6 0\<newline>e 7 8  9 0 \<newline>''"

lemma non_increasing_prefix [simp]:
  assumes "prefix s = Some (pre, s')"
  shows "length s' \<le> length s" using assms
proof (cases "quant_sets s")
  case None
  hence "prefix s = Some (Empty, s)" by simp
  hence "s' = s" using assms by simp
  thus "length s' \<le> length s" by simp
next
  case (Some a)
  obtain pre s'' where a_def: "a = (pre, s'')" by fastforce
  hence "s' = s''" using Some assms by (cases "convert_quant_sets pre") auto
  moreover have "length s'' < length s" using Some a_def by simp
  ultimately show "length s' \<le> length s" by simp
qed

(* Parser <problem_line> ::= p cnf <pnum> <pnum> EOL; whitespace allowed *)
fun problem_line :: "(nat \<times> nat) parser" where
  "problem_line str = (case match ''p'' (trim_ws str) of
    None \<Rightarrow> None |
    Some (_, str1) \<Rightarrow>
      (case match ''cnf'' (trim_ws str1) of
        None \<Rightarrow> None |
        Some (_, str2) \<Rightarrow>
          (case pnum (trim_ws str2) of
            None \<Rightarrow> None |
            Some (lits, str3) \<Rightarrow>
              (case pnum (trim_ws str3) of
                None \<Rightarrow> None |
                Some (clauses, str4) \<Rightarrow>
                  (case match ''\<newline>'' (trim_ws str4) of
                    None \<Rightarrow> None |
                    Some (_, str5) \<Rightarrow> Some ((lits, clauses), str5))))))"

text \<open>Simple tests.\<close>

value "problem_line ''p cnf 123 321\<newline>''"
value "problem_line ''p   cnf   123 321\<newline>''"
value "problem_line ''p cnf 123 -321\<newline>''"
value "problem_line ''  p cnf 123 321\<newline>''"

lemma decreasing_problem_line [simp]:
  assumes "problem_line s = Some (res, s')"
  shows "length s' < length s"
proof (cases "match ''p'' (trim_ws s)")
  case None
  hence False using assms by simp
  thus ?thesis by simp
next
  case Some_a: (Some a)
  obtain u s1 where a_def: "a = (u, s1)" by (meson surj_pair)
  hence le1: "length s1 \<le> length s" using Some_a by fastforce
  show ?thesis
  proof (cases "match ''cnf'' (trim_ws s1)")
    case None
    hence False using Some_a a_def assms by simp
    thus ?thesis by simp
  next
    case Some_b: (Some b)
    obtain u s2 where b_def: "b = (u, s2)" by (meson surj_pair)
    hence le2: "length s2 \<le> length s1" using Some_b by fastforce
    show ?thesis
    proof (cases "pnum (trim_ws s2)")
      case None
      hence False using Some_a a_def Some_b b_def assms by simp
      thus ?thesis by simp
    next
      case Some_c: (Some c)
      obtain lits s3 where c_def: "c = (lits, s3)" by fastforce
      hence less1: "length s3 < length s2" using Some_c by fastforce
      show ?thesis
      proof (cases "pnum (trim_ws s3)")
        case None
        hence False using Some_a a_def Some_b b_def Some_c c_def assms by simp
        thus ?thesis by simp
      next
        case Some_d: (Some d)
        obtain clauses s4 where d_def: "d = (clauses, s4)" by fastforce
        hence less2: "length s4 < length s3" using Some_d by fastforce
        show ?thesis
        proof (cases "match ''\<newline>'' (trim_ws s4)")
          case None
          hence False using Some_a a_def Some_b b_def Some_c c_def Some_d d_def assms by simp
          thus ?thesis by simp
        next
          case Some_e: (Some e)
          obtain u s5 where e_def: "e = (u, s5)" by (meson surj_pair)
          hence "problem_line s = Some ((lits, clauses), s5)"
            using Some_a a_def Some_b b_def Some_c c_def Some_d d_def Some_e by simp
          hence "s' = s5" using assms by simp
          hence "match ''\<newline>'' (trim_ws s4) = Some (u, s')" using Some_e e_def by simp
          hence "length s' \<le> length s4" by fastforce
          thus "length s' < length s" using le1 le2 less1 less2 by simp
        qed
      qed
    qed
  qed
qed

(* Parse <text> *)
fun consume_text :: "unit parser" where
  "consume_text Nil = Some ((), Nil)" |
  "consume_text (Cons x xs) = (if x = CHR ''\<newline>'' then Some ((), Cons x xs) else consume_text xs)"

lemma non_increasing_consume_text [simp]: "consume_text s = Some ((), s') \<Longrightarrow> length s' \<le> length s"
  apply (induction s rule: consume_text.induct)
   apply simp
  by (metis (mono_tags, lifting) consume_text.simps(2) le_imp_less_Suc length_Cons nle_le option.sel order_less_imp_le prod.sel(2))

(* Parse <comment_line> ::= c <text> EOL; whitespace allowed *)
fun comment_line :: "unit parser" where
  "comment_line str = (case match ''c'' (trim_ws str) of
    None \<Rightarrow> None |
    Some (_, str') \<Rightarrow>
      (case consume_text str' of
        None \<Rightarrow> None |
        Some (_, str'') \<Rightarrow>
          (case match ''\<newline>'' str'' of
            None \<Rightarrow> None |
            Some (_, str''') \<Rightarrow> Some ((), str'''))))"

text \<open>Simple tests.\<close>

value "comment_line ''c e 1 2 3\<newline>e 1 2 3''"
value "comment_line ''e 1 2 3\<newline>e 1 2 3''"
value "comment_line ''  c  e  1  2   3  \<newline>e 1 2 3''"

lemma decreasing_comment_line [simp]:
  assumes "comment_line s = Some ((), s')"
  shows "length s' < length s"
proof (cases "match ''c'' (trim_ws s)")
  case None
  hence False using assms by simp
  thus ?thesis by simp
next
  case Some_a: (Some a)
  obtain u s1 where a_def: "a = (u, s1)" by (meson surj_pair)
  hence less1: "length s1 < length s"
    using Some_a decreasing_match[of "''c''" "trim_ws s" s1] by fastforce
  show ?thesis
  proof (cases "consume_text s1")
    case None
    hence False using Some_a a_def assms by simp
    thus ?thesis by simp
  next
    case Some_b: (Some b)
    obtain u s2 where b_def: "b = (u, s2)" by (meson surj_pair)
    hence le1: "length s2 \<le> length s1" using Some_b by simp
    show ?thesis
    proof (cases "match ''\<newline>'' s2")
      case None
      hence False using Some_a a_def Some_b b_def assms by simp
      thus ?thesis by simp
    next
      case Some_c: (Some c)
      obtain u s3 where c_def: "c = (u, s3)" by (meson surj_pair)
      hence "comment_line s = Some (u, s3)" using Some_a a_def Some_b b_def Some_c by simp
      hence "s3 = s'" using assms by simp
      hence "match ''\<newline>'' s2 = Some (u, s')" using Some_c c_def by simp
      hence "length s' \<le> length s2" by simp
      thus "length s' < length s" using less1 le1 by simp
    qed
  qed
qed

(* Parse <comment_lines> ::= <comment_line> <comment_lines> | <comment_line>; no whitespace *)
fun comment_lines :: "unit parser" where
  "comment_lines str = (case comment_line str of
    None \<Rightarrow> None |
    Some (_, str') \<Rightarrow>
      (case comment_lines str' of
        None \<Rightarrow> Some ((), str') |
        Some (_, str'') \<Rightarrow> Some ((), str'')))"

text \<open>Simple tests.\<close>

value "comment_lines ''c a comment\<newline>c another comment\<newline>''"
value "comment_lines ''c a comment\<newline>  c another comment\<newline>''"

lemma decreasing_comment_lines [simp]:
  assumes "comment_lines s = Some ((), s')"
  shows "length s' < length s" using assms
proof (induction s rule: comment_lines.induct)
  case (1 s)
  show ?case
  proof (cases "comment_line s")
    case None
    hence False using 1 by simp
    thus ?thesis by simp
  next
    case Some_a: (Some a)
    obtain u s1 where a_def: "a = (u, s1)" by (meson surj_pair)
    hence less1: "length s1 < length s" using Some_a by simp
    show ?thesis
    proof (cases "comment_lines s1")
      case None
      hence "comment_lines s = Some ((), s1)" using Some_a a_def by simp
      hence "s1 = s'" using 1 by simp
      thus "length s' < length s" using less1 by simp
    next
      case Some_b: (Some b)
      obtain u s2 where b_def: "b = (u, s2)" by (meson surj_pair)
      hence "comment_lines s = Some ((), s2)" using Some_a a_def Some_b by simp
      hence "s2 = s'" using 1 by simp
      hence "comment_lines s1 = Some ((), s')" using Some_a a_def Some_b b_def by simp
      hence "length s' < length s1" using 1 Some_a a_def by blast
      thus "length s' < length s" using less1 by simp
    qed
  qed
qed

(* Parse <preamble> ::= [<comment_lines>] <problem_line>; no whitespace *)
fun preamble :: "(nat \<times> nat) parser" where
  "preamble str = (case comment_lines str of
    None \<Rightarrow> problem_line str |
    Some (_, str') \<Rightarrow> problem_line str')"

text \<open>Simple tests.\<close>

value "preamble ''c an example\<newline>p cnf 4 5\<newline>''"
value "preamble '' c  an  example\<newline>  p cnf 4 5\<newline>''"

lemma decreasing_preamble [simp]:
  assumes "preamble s = Some (p, s')"
  shows "length s' < length s"
proof (cases "comment_lines s")
  case None
  hence "preamble s = problem_line s" by simp
  thus ?thesis using assms by simp
next
  case (Some a)
  obtain p s'' where a_def: "a = (p, s'')" by (meson surj_pair)
  hence "preamble s = problem_line s''" using Some by simp
  hence "length s' < length s''" using assms by simp
  moreover have "length s'' < length s" using Some a_def by simp
  ultimately show "length s' < length s" by simp
qed

(* Check if all input has been consumed; used instead of EOF token *)
fun eof :: "unit parser" where
  "eof Nil = Some ((), Nil)"
| "eof (Cons x xs) = None"

lemma eof_nil [simp]: "eof s = Some ((), s') \<Longrightarrow> s' = Nil"
  by (cases s) auto

(* Parse <input> ::= <preamble> <prefix> <matrix> EOF; no whitespace *)
fun input :: "PCNF.pcnf parser" where
  "input str = (case preamble str of
    None \<Rightarrow> None |
    Some ((lits, clauses), str') \<Rightarrow>
      (case prefix str' of
        None \<Rightarrow> None |
        Some (pre, str'') \<Rightarrow>
          (case matrix str'' of
            None \<Rightarrow> None |
            Some (mat, str''') \<Rightarrow>
              (case eof str''' of
                None \<Rightarrow> None |
                Some (_, str'''') \<Rightarrow> Some ((pre, mat), str'''')))))"

text \<open>Simple tests.\<close>

value "input
''c an example from the QDIMACS specification
c multiple
c lines
cwith
c comments
p cnf 4 2
e 1 2 3 4 0
-1  2 0
2 -3 -4 0
''"

value "input
''c an extension of the example from the QDIMACS specification
c multiple
c lines
cwith
c comments
p cnf 40 4
e 1 2 3 4 0
a 11 12 13 14 0
e 21 22 23 24 0
-1  2 0
2 -3 -4 0
40 -13 -24 0
12 -23 -24 0
''"

lemma input_nil [simp]:
  assumes "input s = Some (p, s')"
  shows "s' = Nil" using assms
proof (cases "preamble s")
  case None
  hence False using assms by simp
  thus ?thesis by simp
next
  case Some_a: (Some a)
  obtain p s1 where a_def: "a = (p, s1)" by (meson surj_pair)
  show ?thesis
  proof (cases "prefix s1")
    case None
    hence False using Some_a a_def assms by simp
    thus ?thesis by simp
  next
    case Some_b: (Some b)
    obtain pre s2 where b_def: "b = (pre, s2)" by fastforce
    show ?thesis
    proof (cases "matrix s2")
      case None
      hence False using Some_a a_def Some_b b_def assms by simp
      thus ?thesis by simp
    next
      case Some_c: (Some c)
      obtain mat s3 where c_def: "c = (mat, s3)" by fastforce
      show ?thesis
      proof (cases "eof s3")
        case None
        hence False using Some_a a_def Some_b b_def Some_c c_def assms by simp
        thus ?thesis by simp
      next
        case Some_d: (Some d)
        obtain u s4 where d_def: "d = (u, s4)" by (meson surj_pair)
        hence "input s = Some ((pre, mat), s4)"
          using Some_a a_def Some_b b_def Some_c c_def Some_d d_def by simp
        hence "s4 = s'" using assms by simp
        moreover have "s4 = Nil" using Some_d d_def by simp
        ultimately show "s' = Nil" by simp
      qed
    qed
  qed
qed

(* Parse (superset of) QDIMACS files *)
fun parse :: "String.literal \<Rightarrow> pcnf option" where
  "parse str = map_option fst (input (String.explode str))"

text \<open>Simple tests.\<close>

value "parse (String.implode
''c an example from the QDIMACS specification
c multiple
c lines
cwith
c comments
p cnf 4 2
e 1 2 3 4 0
-1  2 0
2 -3 -4 0
'')"

value "parse (String.implode
''c an extension of the example from the QDIMACS specification
c multiple
c lines
cwith
c comments
p cnf 40 4
e 1 2 3 4 0
a 11 12 13 14 0
e 21 22 23 24 0
-1  2 0
2 -3 -4 0
40 -13 -24 0
12 -23 -24 0
'')"

end