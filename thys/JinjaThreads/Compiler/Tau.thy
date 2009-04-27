(*  Title:      JinjaThreads/Compiler/Tau.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Unobservable steps} *}

theory Tau imports Compiler2_AddOn "../JVM/JVMDefensive" begin

declare match_ex_table_append_not_pcs[simp del]
  outside_pcs_not_matches_entry [simp del]
  outside_pcs_compxE2_not_matches_entry [simp del]
  outside_pcs_compxEs2_not_matches_entry [simp del]


inductive \<tau>move1 :: "('a, 'b) exp \<Rightarrow> bool"
  and \<tau>moves1 :: "('a, 'b) exp list \<Rightarrow> bool"
where
  \<tau>move1NewArray: "\<tau>move1 e \<Longrightarrow> \<tau>move1 (newA T\<lfloor>e\<rceil>)"
| \<tau>move1Cast: "\<tau>move1 e \<Longrightarrow> \<tau>move1 (Cast U e)"
| \<tau>move1BinOp1: "\<tau>move1 e \<Longrightarrow> \<tau>move1 (e\<guillemotleft>bop\<guillemotright>e2)"
| \<tau>move1BinOp2: "\<tau>move1 e \<Longrightarrow> \<tau>move1 (Val v\<guillemotleft>bop\<guillemotright>e)"
| \<tau>move1LAss: "\<tau>move1 e \<Longrightarrow> \<tau>move1 (V := e)"
| \<tau>move1AAcc1: "\<tau>move1 a \<Longrightarrow> \<tau>move1 (a\<lfloor>i\<rceil>)"
| \<tau>move1AAcc2: "\<tau>move1 i \<Longrightarrow> \<tau>move1 (Val a\<lfloor>i\<rceil>)"
| \<tau>move1AAss1: "\<tau>move1 a \<Longrightarrow> \<tau>move1 (a\<lfloor>i\<rceil> := e)"
| \<tau>move1AAss2: "\<tau>move1 i \<Longrightarrow> \<tau>move1 (Val a\<lfloor>i\<rceil> := e)"
| \<tau>move1AAss3: "\<tau>move1 e \<Longrightarrow> \<tau>move1 (Val a\<lfloor>Val i\<rceil> := e)"
| \<tau>move1ALength: "\<tau>move1 a \<Longrightarrow> \<tau>move1 (a\<bullet>length)"
| \<tau>move1FAcc: "\<tau>move1 e \<Longrightarrow> \<tau>move1 (e\<bullet>F{D})"
| \<tau>move1FAss1: "\<tau>move1 e \<Longrightarrow> \<tau>move1 (e\<bullet>F{D} := e')"
| \<tau>move1FAss2: "\<tau>move1 e \<Longrightarrow> \<tau>move1 (Val v\<bullet>F{D} := e)"
| \<tau>move1CallObj: "\<tau>move1 obj \<Longrightarrow> \<tau>move1 (obj\<bullet>M(ps))"
| \<tau>move1CallParams: "\<tau>moves1 ps \<Longrightarrow> \<tau>move1 (Val v\<bullet>M(ps))"
| \<tau>move1Block: "\<tau>move1 e \<Longrightarrow> \<tau>move1 {V:T=vo; e}\<^bsub>cr\<^esub>"
| \<tau>move1BlockRed: "\<tau>move1 {V:T=vo; Val v}\<^bsub>False\<^esub>"
| \<tau>move1Sync: "\<tau>move1 o' \<Longrightarrow> \<tau>move1 (sync\<^bsub>V\<^esub> (o') e)"
| \<tau>move1InSync: "\<tau>move1 e \<Longrightarrow> \<tau>move1 (insync\<^bsub>V\<^esub> (a) e)"
| \<tau>move1Seq: "\<tau>move1 e \<Longrightarrow> \<tau>move1 (e;;e2)"
| \<tau>move1Cond: "\<tau>move1 e \<Longrightarrow> \<tau>move1 (if (e) e1 else e2)"
| \<tau>move1WhileRed: "\<tau>move1 (while (c) e)"
| \<tau>move1Throw: "\<tau>move1 e \<Longrightarrow> \<tau>move1 (throw e)"
| \<tau>move1ThrowNull: "\<tau>move1 (throw null)"
| \<tau>move1Try: "\<tau>move1 e \<Longrightarrow> \<tau>move1 (try e catch(C V) e'')"
| \<tau>move1TryCatch: "\<tau>move1 (try Throw a catch(C V) e)"
| \<tau>move1TryFail: "\<tau>move1 (try Throw a catch(C V) e)"
| \<tau>move1TryRed: "\<tau>move1 (try Val v catch(C V) e)"
| \<tau>move1NewArrayThrow: "\<tau>move1 (newA T\<lfloor>Throw a\<rceil>)"
| \<tau>move1CastThrow: "\<tau>move1 (Cast T (Throw a))"
| \<tau>move1BinOpThrow1: "\<tau>move1 (Throw a \<guillemotleft>bop\<guillemotright> e2)"
| \<tau>move1BinOpThrow2: "\<tau>move1 (Val v \<guillemotleft>bop\<guillemotright> Throw a)"
| \<tau>move1LAssThrow: "\<tau>move1 (V:=(Throw a))"
| \<tau>move1AAccThrow1: "\<tau>move1 (Throw a\<lfloor>e\<rceil>)"
| \<tau>move1AAccThrow2: "\<tau>move1 (Val v\<lfloor>Throw a\<rceil>)"
| \<tau>move1AAssThrow1: "\<tau>move1 (Throw a\<lfloor>e\<rceil> := e')"
| \<tau>move1AAssThrow2: "\<tau>move1 (Val v\<lfloor>Throw a\<rceil> := e')"
| \<tau>move1AAssThrow3: "\<tau>move1 (Val v\<lfloor>Val v'\<rceil> := Throw a)"
| \<tau>move1ALengthThrow: "\<tau>move1 (Throw a\<bullet>length)"
| \<tau>move1FAccThrow: "\<tau>move1 (Throw a\<bullet>F{D})"
| \<tau>move1FAssThrow1: "\<tau>move1 (Throw a\<bullet>F{D} := e)"
| \<tau>move1FAssThrow2: "\<tau>move1 (Val v\<bullet>F{D} := Throw a)"
| \<tau>move1BlockThrow: "\<tau>move1 {V:T=vo; Throw a}\<^bsub>False\<^esub>"
| \<tau>move1SyncThrow: "\<tau>move1 (sync\<^bsub>V\<^esub> (Throw a) e)"
| \<tau>move1SeqThrow: "\<tau>move1 (Throw a;;e)"
| \<tau>move1CondThrow: "\<tau>move1 (if (Throw a) e1 else e2)"
| \<tau>move1ThrowThrow: "\<tau>move1 (throw (Throw a))"
| \<tau>move1CallThrowObj: "\<tau>move1 (Throw a\<bullet>M(es))"
| \<tau>move1CallThrowParams: "\<tau>move1 (Val v\<bullet>M(map Val vs @ Throw a # es))"

| \<tau>moves1Hd: "\<tau>move1 e \<Longrightarrow> \<tau>moves1 (e # es)"
| \<tau>moves1Tl: "\<tau>moves1 es \<Longrightarrow> \<tau>moves1 (Val v # es)"

lemma \<tau>move1_Val [dest!]:
  "\<tau>move1 (Val v) \<Longrightarrow> False"
by(auto elim: \<tau>move1.cases)

inductive_cases \<tau>move1_cases [elim]:
  "\<tau>move1 (new C)"
  "\<tau>move1 (newA T\<lfloor>e\<rceil>)"
  "\<tau>move1 (Cast T e)"
  "\<tau>move1 (e1 \<guillemotleft>bop\<guillemotright> e2)"
  "\<tau>move1 (V := e)"
  "\<tau>move1 (a\<lfloor>i\<rceil>)"
  "\<tau>move1 (AAss a i e)"
  "\<tau>move1 (a\<bullet>length)"
  "\<tau>move1 (e\<bullet>F{D})"
  "\<tau>move1 (FAss e F D e')"
  "\<tau>move1 (obj\<bullet>M(ps))"
  "\<tau>move1 ({V:T=vo; e}\<^bsub>cr\<^esub>)"
  "\<tau>move1 (sync\<^bsub>V\<^esub> (o') e)"
  "\<tau>move1 (insync\<^bsub>V\<^esub> (a) e)"
  "\<tau>move1 (e1;;e2)"
  "\<tau>move1 (if (e) e1 else e2)"
  "\<tau>move1 (while (b) c)"
  "\<tau>move1 (throw e)"
  "\<tau>move1 (try e catch(C V) e')"
  "\<tau>move1 (Var V)"
  "\<tau>move1 (Val v)"

inductive_cases \<tau>moves1_cases [elim]:
  "\<tau>moves1 (e # es)"

lemma \<tau>moves1_Nil [dest!]:
  "\<tau>moves1 [] \<Longrightarrow> False"
by(auto elim: \<tau>moves1.cases)

lemma \<tau>moves1_map_Val [dest!]:
  "\<tau>moves1 (map Val es) \<Longrightarrow> False"
by(induct es)(erule \<tau>moves1.cases \<tau>move1.cases, auto)+

lemma fixes e :: "('a, 'b) exp"
  and es :: "('a, 'b) exp list"
  shows \<tau>move1_not_call: "\<tau>move1 e \<Longrightarrow> call e = None"
  and \<tau>moves1_not_calls: "\<tau>moves1 es \<Longrightarrow> calls es = None"
apply(induct e and es)
apply(auto simp add: is_vals_conv elim!: \<tau>move1_cases)
apply(drule sym)
apply(auto simp add: append_eq_conv_conj drop_map)
done

lemma red1_\<tau>_taD: "\<lbrakk> P \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; \<tau>move1 e \<rbrakk> \<Longrightarrow> ta = \<epsilon>"
  and reds1_\<tau>_taD: "\<lbrakk> P \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; \<tau>moves1 es \<rbrakk> \<Longrightarrow> ta = \<epsilon>"
apply(induct rule: red1_reds1.inducts)
apply(fastsimp simp add: map_eq_append_conv)+
done

lemma \<tau>move1_heap_unchanged: "\<lbrakk> P \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; \<tau>move1 e \<rbrakk> \<Longrightarrow> hp s' = hp s"
  and \<tau>moves1_heap_unchanged: "\<lbrakk> P \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; \<tau>moves1 es \<rbrakk> \<Longrightarrow> hp s' = hp s"
apply(induct rule: red1_reds1.inducts)
apply(auto)
apply(fastsimp simp add: map_eq_append_conv)
done

lemma red1_hext:
  "\<lbrakk> P \<turnstile>1 \<langle>e, s\<rangle> -\<epsilon>\<rightarrow> \<langle>e', s'\<rangle>; hp s = hp s'; hext (hp s) h; \<tau>move1 e \<rbrakk>
  \<Longrightarrow> P \<turnstile>1 \<langle>e, (h, lcl s)\<rangle> -\<epsilon>\<rightarrow> \<langle>e', (h, lcl s')\<rangle>"

  and reds1_hext:
  "\<lbrakk> P \<turnstile>1 \<langle>es, s\<rangle> [-\<epsilon>\<rightarrow>] \<langle>es', s'\<rangle>; hp s = hp s'; hext (hp s) h; \<tau>moves1 es \<rbrakk>
  \<Longrightarrow> P \<turnstile>1 \<langle>es, (h, lcl s)\<rangle> [-\<epsilon>\<rightarrow>] \<langle>es', (h, lcl s')\<rangle>"
proof(induct e s ta\<equiv>"\<epsilon> :: J1_thread_action" e' s'
        and es s ta\<equiv>"\<epsilon> :: J1_thread_action" es' s'
       rule: red1_reds1.inducts)
  case Red1New thus ?case by(fastsimp dest: new_Addr_SomeD simp add: expand_fun_eq split: split_if_asm)
next
  case Red1NewFail thus ?case
    by(fastsimp simp add: new_Addr_def dest: hext_objarrD split: split_if_asm intro!: red1_reds1.Red1NewFail)
next
  case Red1TryCatch thus ?case by(auto dest: hext_objD intro: red1_reds1.intros)
next
  case Red1TryFail thus ?case by(auto dest!: hext_objD)(auto intro: red1_reds1.intros)
next
  case Red1CallExternal thus ?case by(fastsimp simp add: map_eq_append_conv)
qed(fastsimp intro: red1_reds1.intros simp add: expand_finfun_eq expand_fun_eq finfun_upd_apply split: split_if_asm)+


inductive \<tau>move2 :: "expr1 \<Rightarrow> nat \<Rightarrow> addr option \<Rightarrow> bool"
  and \<tau>moves2 :: "expr1 list \<Rightarrow> nat \<Rightarrow> addr option \<Rightarrow> bool"
where
  \<tau>move2xcp: "pc < length (compE2 e) \<Longrightarrow> \<tau>move2 e pc \<lfloor>xcp\<rfloor>"

| \<tau>move2NewArray: "\<tau>move2 e pc xcp \<Longrightarrow> \<tau>move2 (newA T\<lfloor>e\<rceil>) pc xcp"

| \<tau>move2Cast: "\<tau>move2 e pc xcp \<Longrightarrow> \<tau>move2 (Cast T e) pc xcp"

| \<tau>move2Val: "\<tau>move2 (Val v) 0 None"

| \<tau>move2BinOp1:
  "\<tau>move2 e1 pc xcp \<Longrightarrow> \<tau>move2 (e1\<guillemotleft>bop\<guillemotright>e2) pc xcp"
| \<tau>move2BinOp2:
  "\<tau>move2 e2 pc xcp \<Longrightarrow> \<tau>move2 (e1\<guillemotleft>bop\<guillemotright>e2) (length (compE2 e1) + pc) xcp"

| \<tau>move2LAss:
  "\<tau>move2 e pc xcp \<Longrightarrow> \<tau>move2 (V:=e) pc xcp"
| \<tau>move2LAssRed:
  "\<tau>move2 (V:=e) (Suc (length (compE2 e))) None"

| \<tau>move2AAcc1: "\<tau>move2 a pc xcp \<Longrightarrow> \<tau>move2 (a\<lfloor>i\<rceil>) pc xcp"
| \<tau>move2AAcc2: "\<tau>move2 i pc xcp \<Longrightarrow> \<tau>move2 (a\<lfloor>i\<rceil>) (length (compE2 a) + pc) xcp"

| \<tau>move2AAss1: "\<tau>move2 a pc xcp \<Longrightarrow> \<tau>move2 (a\<lfloor>i\<rceil> := e) pc xcp"
| \<tau>move2AAss2: "\<tau>move2 i pc xcp \<Longrightarrow> \<tau>move2 (a\<lfloor>i\<rceil> := e) (length (compE2 a) + pc) xcp"
| \<tau>move2AAss3: "\<tau>move2 e pc xcp \<Longrightarrow> \<tau>move2 (a\<lfloor>i\<rceil> := e) (length (compE2 a) + length (compE2 i) + pc) xcp"
| \<tau>move2AAssRed: "\<tau>move2 (a\<lfloor>i\<rceil> := e) (Suc (length (compE2 a) + length (compE2 i) + length (compE2 e))) None"

| \<tau>move2ALength: "\<tau>move2 a pc xcp \<Longrightarrow> \<tau>move2 (a\<bullet>length) pc xcp"

| \<tau>move2FAcc: "\<tau>move2 e pc xcp \<Longrightarrow> \<tau>move2 (e\<bullet>F{D}) pc xcp"

| \<tau>move2FAss1: "\<tau>move2 e pc xcp \<Longrightarrow> \<tau>move2 (e\<bullet>F{D} := e') pc xcp"
| \<tau>move2FAss2: "\<tau>move2 e' pc xcp \<Longrightarrow> \<tau>move2 (e\<bullet>F{D} := e') (length (compE2 e) + pc) xcp"
| \<tau>move2FAssRed: "\<tau>move2 (e\<bullet>F{D} := e') (Suc (length (compE2 e) + length (compE2 e'))) None"

| \<tau>move2CallObj:
  "\<tau>move2 obj pc xcp \<Longrightarrow> \<tau>move2 (obj\<bullet>M(ps)) pc xcp"
| \<tau>move2CallParams:
  "\<tau>moves2 ps pc xcp \<Longrightarrow> \<tau>move2 (obj\<bullet>M(ps)) (length (compE2 obj) + pc) xcp"

| \<tau>move2BlockSome1:
  "\<tau>move2 {V:T=\<lfloor>v\<rfloor>; e}\<^bsub>cr\<^esub> 0 None"
| \<tau>move2BlockSome2:
  "\<tau>move2 {V:T=\<lfloor>v\<rfloor>; e}\<^bsub>cr\<^esub> (Suc 0) None"
| \<tau>move2BlockSome:
  "\<tau>move2 e pc xcp \<Longrightarrow> \<tau>move2 {V:T=\<lfloor>v\<rfloor>; e}\<^bsub>cr\<^esub> (Suc (Suc pc)) xcp"
| \<tau>move2BlockNone:
  "\<tau>move2 e pc xcp \<Longrightarrow> \<tau>move2 {V:T=None; e}\<^bsub>cr\<^esub> pc xcp"

| \<tau>move2Sync1:
  "\<tau>move2 o' pc xcp \<Longrightarrow> \<tau>move2 (sync\<^bsub>V\<^esub> (o') e) pc xcp"
| \<tau>move2Sync2:
  "\<tau>move2 (sync\<^bsub>V\<^esub> (o') e) (length (compE2 o')) None"
| \<tau>move2Sync3:
  "\<tau>move2 (sync\<^bsub>V\<^esub> (o') e) (Suc (length (compE2 o'))) None"
| \<tau>move2Sync4:
  "\<tau>move2 e pc xcp \<Longrightarrow> \<tau>move2 (sync\<^bsub>V\<^esub> (o') e) (Suc (Suc (Suc (length (compE2 o') + pc)))) xcp"
| \<tau>move2Sync5:
  "\<tau>move2 (sync\<^bsub>V\<^esub> (o') e) (Suc (Suc (Suc (length (compE2 o') + length (compE2 e))))) None"
| \<tau>move2Sync6:
  "\<tau>move2 (sync\<^bsub>V\<^esub> (o') e) (5 + length (compE2 o') + length (compE2 e)) None"
| \<tau>move2Sync7:
  "\<tau>move2 (sync\<^bsub>V\<^esub> (o') e) (6 + length (compE2 o') + length (compE2 e)) None"
| \<tau>move2Sync8:
  "\<tau>move2 (sync\<^bsub>V\<^esub> (o') e) (8 + length (compE2 o') + length (compE2 e)) None"


| \<tau>move2Seq1:
  "\<tau>move2 e pc xcp \<Longrightarrow> \<tau>move2 (e;;e') pc xcp"
| \<tau>move2Seq2:
  "\<tau>move2 e' pc xcp \<Longrightarrow> \<tau>move2 (e;;e') (Suc (length (compE2 e) + pc)) xcp"

| \<tau>move2Cond:
  "\<tau>move2 e pc xcp \<Longrightarrow> \<tau>move2 (if (e) e1 else e2) pc xcp"
| \<tau>move2CondThen:
  "\<tau>move2 e1 pc xcp
  \<Longrightarrow> \<tau>move2 (if (e) e1 else e2) (Suc (length (compE2 e) + pc)) xcp"
| \<tau>move2CondThenExit:
  "\<tau>move2 (if (e) e1 else e2) (Suc (length (compE2 e) + length (compE2 e1))) None "
| \<tau>move2CondElse:
  "\<tau>move2 e2 pc xcp
  \<Longrightarrow> \<tau>move2 (if (e) e1 else e2) (Suc (Suc (length (compE2 e) + length (compE2 e1) + pc))) xcp "

| \<tau>move2While1:
  "\<tau>move2 c pc xcp \<Longrightarrow> \<tau>move2 (while (c) e) pc xcp"
| \<tau>move2While2:
  "\<tau>move2 e pc xcp \<Longrightarrow> \<tau>move2 (while (c) e) (Suc (length (compE2 c) + pc)) xcp"
| \<tau>move2While3: -- "Jump back to condition"
  "\<tau>move2 (while (c) e) (Suc (Suc (length (compE2 c) + length (compE2 e)))) None"
| \<tau>move2While4: -- "last instruction: Push Unit"
  "\<tau>move2 (while (c) e) (Suc (Suc (Suc (length (compE2 c) + length (compE2 e))))) None"

| \<tau>move2Throw1:
  "\<tau>move2 e pc xcp \<Longrightarrow> \<tau>move2 (throw e) pc xcp"
| \<tau>move2Throw2:
  "\<tau>move2 (throw e) (length (compE2 e)) None"

| \<tau>move2Try1:
  "\<tau>move2 e pc xcp \<Longrightarrow> \<tau>move2 (try e catch(C V) e') pc xcp"
| \<tau>move2TryJump:
  "\<tau>move2 (try e catch(C V) e') (length (compE2 e)) None"
| \<tau>move2TryCatch2:
  "\<tau>move2 (try e catch(C V) e') (Suc (length (compE2 e))) None"
| \<tau>move2Try2:
  "\<tau>move2 {V:T=None; e'}\<^bsub>False\<^esub> pc xcp
  \<Longrightarrow> \<tau>move2 (try e catch(C V) e') (Suc (Suc (length (compE2 e) + pc))) xcp"

| \<tau>moves2Hd:
  "\<tau>move2 e pc xcp \<Longrightarrow> \<tau>moves2 (e # es) pc xcp"
| \<tau>moves2Tl:
  "\<tau>moves2 es pc xcp \<Longrightarrow> \<tau>moves2 (e # es) (length (compE2 e) + pc) xcp"

inductive_cases \<tau>move2_cases:
  "\<tau>move2 (new C) pc xcp"
  "\<tau>move2 (newA T\<lfloor>e\<rceil>) pc xcp"
  "\<tau>move2 (Cast T e) pc xcp"
  "\<tau>move2 (Val v) pc xcp"
  "\<tau>move2 (Var V) pc xcp"
  "\<tau>move2 (e1\<guillemotleft>bop\<guillemotright>e2) pc xcp"
  "\<tau>move2 (V := e) pc xcp"
  "\<tau>move2 (e1\<lfloor>e2\<rceil>) pc xcp"
  "\<tau>move2 (e1\<lfloor>e2\<rceil> := e3) pc xcp"
  "\<tau>move2 (e1\<bullet>length) pc xcp"
  "\<tau>move2 (e1\<bullet>F{D}) pc xcp"
  "\<tau>move2 (e1\<bullet>F{D} := e3) pc xcp"
  "\<tau>move2 (e\<bullet>M(ps)) pc xcp"
  "\<tau>move2 {V:T=vo; e}\<^bsub>cr\<^esub> pc xcp"
  "\<tau>move2 (sync\<^bsub>V\<^esub> (e1) e2) pc xcp"
  "\<tau>move2 (e1;;e2) pc xcp"
  "\<tau>move2 (if (e1) e2 else e3) pc xcp"
  "\<tau>move2 (while (e1) e2) pc xcp"
  "\<tau>move2 (try e1 catch(C V) e2) pc xcp"
  "\<tau>move2 (throw e) pc xcp"

lemma \<tau>move2_pc_length_compE2: "\<tau>move2 e pc xcp \<Longrightarrow> pc < length (compE2 e)"
  and \<tau>moves2_pc_length_compEs2: "\<tau>moves2 es pc xcp \<Longrightarrow> pc < length (compEs2 es)"
by(induct rule: \<tau>move2_\<tau>moves2.inducts)(auto)

lemma \<tau>move2_pc_length_compE2_conv: "pc \<ge> length (compE2 e) \<Longrightarrow> \<not> \<tau>move2 e pc xcp"
by(auto dest: \<tau>move2_pc_length_compE2)

lemma \<tau>moves2_pc_length_compEs2_conv: "pc \<ge> length (compEs2 es) \<Longrightarrow> \<not> \<tau>moves2 es pc xcp"
by(auto dest: \<tau>moves2_pc_length_compEs2)


lemma \<tau>moves2_append [elim]:
  "\<tau>moves2 es pc xcp \<Longrightarrow> \<tau>moves2 (es @ es') pc xcp"
apply(induct es arbitrary: pc pc')
apply(erule \<tau>moves2.cases, auto elim: intro: \<tau>move2_\<tau>moves2.intros)+
done

lemma append_\<tau>moves2:
  "\<tau>moves2 es pc xcp \<Longrightarrow> \<tau>moves2 (es' @ es) (length (compEs2 es') + pc) xcp"
by(induct es')(auto intro: \<tau>move2_\<tau>moves2.intros simp add: add_assoc)

lemma \<tau>moves2xcp: "pc < length (compEs2 es) \<Longrightarrow> \<tau>moves2 es pc \<lfloor>xcp\<rfloor>"
proof(induct es arbitrary: pc)
  case Nil thus ?case by simp
next
  case (Cons e es)
  note IH = `\<And>pc. pc < length (compEs2 es) \<Longrightarrow> \<tau>moves2 es pc \<lfloor>xcp\<rfloor>`
  note pc = `pc < length (compEs2 (e # es))`
  show ?case
  proof(cases "pc < length (compE2 e)")
    case True
    thus ?thesis by(auto intro: \<tau>moves2Hd \<tau>move2xcp)
  next
    case False
    with pc IH[of "pc - length (compE2 e)"]
    have "\<tau>moves2 es (pc - length (compE2 e)) \<lfloor>xcp\<rfloor>" by(simp)
    hence "\<tau>moves2 (e # es) (length (compE2 e) + (pc - length (compE2 e))) \<lfloor>xcp\<rfloor>"
      by(rule \<tau>moves2Tl)
    with False show ?thesis by simp
  qed
qed

lemma [dest]:
  shows \<tau>move2_NewArrayD: "\<lbrakk> \<tau>move2 (newA T\<lfloor>e\<rceil>) pc xcp; pc < length (compE2 e) \<rbrakk> \<Longrightarrow> \<tau>move2 e pc xcp"
  and \<tau>move2_CastD: "\<lbrakk> \<tau>move2 (Cast T e) pc xcp; pc < length (compE2 e) \<rbrakk> \<Longrightarrow> \<tau>move2 e pc xcp"
  and \<tau>move2_BinOp1D: "\<lbrakk> \<tau>move2 (e1 \<guillemotleft>bop\<guillemotright> e2) pc' xcp'; pc' < length (compE2 e1) \<rbrakk> \<Longrightarrow> \<tau>move2 e1 pc' xcp'"
  and \<tau>move2_BinOp2D:
  "\<lbrakk> \<tau>move2 (e1 \<guillemotleft>bop\<guillemotright> e2) (length (compE2 e1) + pc') xcp'; pc' < length (compE2 e2) \<rbrakk> \<Longrightarrow> \<tau>move2 e2 pc' xcp'"
  and \<tau>move2_LAssD: "\<lbrakk> \<tau>move2 (V := e) pc xcp; pc < length (compE2 e) \<rbrakk> \<Longrightarrow> \<tau>move2 e pc xcp"
  and \<tau>move2_AAccD1: "\<lbrakk> \<tau>move2 (a\<lfloor>i\<rceil>) pc xcp; pc < length (compE2 a) \<rbrakk> \<Longrightarrow> \<tau>move2 a pc xcp"
  and \<tau>move2_AAccD2: "\<lbrakk> \<tau>move2 (a\<lfloor>i\<rceil>) (length (compE2 a) + pc) xcp; pc < length (compE2 i) \<rbrakk> \<Longrightarrow> \<tau>move2 i pc xcp"
  and \<tau>move2_AAssD1: "\<lbrakk> \<tau>move2 (a\<lfloor>i\<rceil> := e) pc xcp; pc < length (compE2 a) \<rbrakk> \<Longrightarrow> \<tau>move2 a pc xcp"
  and \<tau>move2_AAssD2: "\<lbrakk> \<tau>move2 (a\<lfloor>i\<rceil> := e) (length (compE2 a) + pc) xcp; pc < length (compE2 i) \<rbrakk> \<Longrightarrow> \<tau>move2 i pc xcp"
  and \<tau>move2_AAssD3:
  "\<lbrakk> \<tau>move2 (a\<lfloor>i\<rceil> := e) (length (compE2 a) + length (compE2 i) + pc) xcp; pc < length (compE2 e) \<rbrakk> \<Longrightarrow> \<tau>move2 e pc xcp"
  and \<tau>move2_ALengthD: "\<lbrakk> \<tau>move2 (a\<bullet>length) pc xcp; pc < length (compE2 a) \<rbrakk> \<Longrightarrow> \<tau>move2 a pc xcp"
  and \<tau>move2_FAccD: "\<lbrakk> \<tau>move2 (e\<bullet>F{D}) pc xcp; pc < length (compE2 e) \<rbrakk> \<Longrightarrow> \<tau>move2 e pc xcp"
  and \<tau>move2_FAssD1: "\<lbrakk> \<tau>move2 (e\<bullet>F{D} := e') pc xcp; pc < length (compE2 e) \<rbrakk> \<Longrightarrow> \<tau>move2 e pc xcp"
  and \<tau>move2_FAssD2: "\<lbrakk> \<tau>move2 (e\<bullet>F{D} := e') (length (compE2 e) + pc) xcp; pc < length (compE2 e') \<rbrakk> \<Longrightarrow> \<tau>move2 e' pc xcp"
  and \<tau>move2_CallObjD: "\<lbrakk> \<tau>move2 (e\<bullet>M(es)) pc xcp; pc < length (compE2 e) \<rbrakk> \<Longrightarrow> \<tau>move2 e pc xcp"
  and \<tau>move2_BlockNoneD: "\<tau>move2 {V:T=None; e}\<^bsub>cr\<^esub> pc xcp \<Longrightarrow> \<tau>move2 e pc xcp"
  and \<tau>move2_BlockSomeD: "\<tau>move2 {V:T=\<lfloor>v\<rfloor>; e}\<^bsub>cr\<^esub> (Suc (Suc pc)) xcp \<Longrightarrow> \<tau>move2 e pc xcp"
  and \<tau>move2_sync1D: "\<lbrakk> \<tau>move2 (sync\<^bsub>V\<^esub> (o') e) pc xcp; pc < length (compE2 o') \<rbrakk> \<Longrightarrow> \<tau>move2 o' pc xcp"
  and \<tau>move2_sync2D:
  "\<lbrakk> \<tau>move2 (sync\<^bsub>V\<^esub> (o') e) (Suc (Suc (Suc (length (compE2 o') + pc)))) xcp; pc < length (compE2 e) \<rbrakk> \<Longrightarrow> \<tau>move2 e pc xcp"
  and \<tau>move2_Seq1D: "\<lbrakk> \<tau>move2 (e1;; e2) pc xcp; pc < length (compE2 e1) \<rbrakk> \<Longrightarrow> \<tau>move2 e1 pc xcp"
  and \<tau>move2_Seq2D: "\<tau>move2 (e1;; e2) (Suc (length (compE2 e1) + pc')) xcp' \<Longrightarrow> \<tau>move2 e2 pc' xcp'"
  and \<tau>move2_IfCondD: "\<lbrakk> \<tau>move2 (if (e) e1 else e2) pc xcp; pc < length (compE2 e) \<rbrakk> \<Longrightarrow> \<tau>move2 e pc xcp"
  and \<tau>move2_IfThenD:
  "\<lbrakk> \<tau>move2 (if (e) e1 else e2) (Suc (length (compE2 e) + pc')) xcp'; pc' < length (compE2 e1) \<rbrakk> \<Longrightarrow> \<tau>move2 e1 pc' xcp'"
  and \<tau>move2_IfElseD:
  "\<tau>move2 (if (e) e1 else e2) (Suc (Suc (length (compE2 e) + length (compE2 e1) + pc'))) xcp' \<Longrightarrow> \<tau>move2 e2 pc' xcp'"
  and \<tau>move2_WhileCondD: "\<lbrakk> \<tau>move2 (while (c) b) pc xcp; pc < length (compE2 c) \<rbrakk> \<Longrightarrow> \<tau>move2 c pc xcp"
  and \<tau>move2_ThrowD: "\<lbrakk> \<tau>move2 (throw e) pc xcp; pc < length (compE2 e) \<rbrakk> \<Longrightarrow> \<tau>move2 e pc xcp"
  and \<tau>move2_Try1D: "\<lbrakk> \<tau>move2 (try e1 catch(C' V) e2) pc xcp; pc < length (compE2 e1) \<rbrakk> \<Longrightarrow> \<tau>move2 e1 pc xcp"
apply(auto elim!: \<tau>move2_cases intro: \<tau>move2xcp dest: \<tau>move2_pc_length_compE2)
done

lemma \<tau>move2_Invoke: "\<lbrakk>\<tau>move2 e pc None; compE2 e ! pc = Invoke M n \<rbrakk> \<Longrightarrow> False"
  and \<tau>moves2_Invoke: "\<lbrakk>\<tau>moves2 es pc None; compEs2 es ! pc = Invoke M n \<rbrakk> \<Longrightarrow> False"
apply(induct e pc xcp\<equiv>"None :: addr option" and es pc xcp\<equiv>"None :: addr option" rule: \<tau>move2_\<tau>moves2.inducts)
apply(simp_all add: nth_append \<tau>move2_pc_length_compE2_conv \<tau>moves2_pc_length_compEs2_conv nth_Cons split: split_if_asm nat.split_asm)
done

lemma \<tau>move2_blocks1 [simp]:
  "\<tau>move2 (blocks1 n Ts body) pc' xcp' = \<tau>move2 body pc' xcp'"
apply(induct n Ts body rule: blocks1.induct)
apply(auto intro: \<tau>move2_\<tau>moves2.intros)
done

lemma \<tau>move2_compE2_not_Invoke: "\<lbrakk> \<tau>move2 e pc None; compE2 e ! pc = Invoke M n\<rbrakk> \<Longrightarrow> False"
  and \<tau>moves2_compEs2_not_Invoke: "\<lbrakk> \<tau>moves2 es pc None; compEs2 es ! pc = Invoke M n\<rbrakk> \<Longrightarrow> False"
apply(induct e and es arbitrary: pc and pc)
apply(fastsimp simp add: nth_append nth_Cons \<tau>move2_pc_length_compE2_conv \<tau>moves2_pc_length_compEs2_conv elim!: \<tau>move2_cases elim: \<tau>moves2.cases split: split_if_asm nat.split_asm)+
done

fun \<tau>Move2 :: "J1_prog \<Rightarrow> jvm_state \<Rightarrow> bool"
where
  "\<tau>Move2 P (xcp, h, []) = False"
| "\<tau>Move2 P (xcp, h, (stk, loc, C, M, pc) # frs) =
       (let (_,_,_,body) = method P C M;
            (_,_,_,_,_,_,xt) = method (compP2 P) C M
        in (\<tau>move2 body pc xcp \<and> (xcp \<noteq> None \<longrightarrow> match_ex_table (compP2 P) (cname_of h (the xcp)) pc xt \<noteq> None)))"


lemma \<tau>Move2_iff:
  "\<tau>Move2 P \<sigma> = (let (xcp, h, frs) = \<sigma>
                 in case frs of [] \<Rightarrow> False
     | (stk, loc, C, M, pc) # frs' \<Rightarrow> 
       (let (_,_,_,body) = method P C M;
            (_,_,_,_,_,_,xt) = method (compP2 P) C M
        in (\<tau>move2 body pc xcp \<and> (xcp \<noteq> None \<longrightarrow> match_ex_table (compP2 P) (cname_of h (the xcp)) pc xt \<noteq> None))))"
by(cases \<sigma>)(clarsimp split: list.splits simp add: expand_fun_eq split_beta)

fun \<tau>Move1 :: "(('a, 'b) exp \<times> 'c) \<times> (('a, 'b) exp \<times> 'd) list \<Rightarrow> bool"
where
  "\<tau>Move1 ((e, x), exs) = \<tau>move1 e"

lemma \<tau>Move1_iff:
  "\<tau>Move1 exexs \<longleftrightarrow> (let ((e, _), _) = exexs in \<tau>move1 e)"
by(cases exexs)(auto)

end