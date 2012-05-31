(*  Title:      JinjaThreads/Execute/ToString.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{String representation of types} *}
theory ToString imports 
  "../J/Expr"
  "../JVM/JVMInstructions"
  "../../Collections/impl/TrieMapImpl"
  "../../Collections/impl/RBTMapImpl"
  "../../Collections/common/Assoc_List"
begin

class toString =
  fixes toString :: "'a \<Rightarrow> String.literal"

instantiation bool :: toString begin
definition [code]: "toString b = (case b of True \<Rightarrow> STR ''True'' | False \<Rightarrow> STR ''False'')"
instance proof qed
end

instantiation char :: toString begin
definition [code]: "toString (c :: char) = implode [c]"
instance proof qed
end

instantiation String.literal :: toString begin
definition [code]: "toString (s :: String.literal) = s"
instance proof qed
end

fun list_toString :: "String.literal \<Rightarrow> 'a :: toString list \<Rightarrow> String.literal list"
where
  "list_toString sep [] = []"
| "list_toString sep [x] = [toString x]"
| "list_toString sep (x#xs) = toString x # sep # list_toString sep xs"

instantiation list :: (toString) toString begin
definition [code]:
  "toString (xs :: 'a list) = Aux.concat (STR ''['' # list_toString (STR '','') xs @ [STR '']''])"
instance proof qed
end

function digit_toString :: "int \<Rightarrow> String.literal"
where
  "digit_toString 0 = STR ''0''"
| "digit_toString 1 = STR ''1''"
| "digit_toString 2 = STR ''2''"
| "digit_toString 3 = STR ''3''"
| "digit_toString 4 = STR ''4''"
| "digit_toString 5 = STR ''5''"
| "digit_toString 6 = STR ''6''"
| "digit_toString 7 = STR ''7''"
| "digit_toString 8 = STR ''8''"
| "digit_toString 9 = STR ''9''"
| "n \<notin> {0, 1, 2, 3, 4, 5, 6, 7, 8, 9} \<Longrightarrow> digit_toString n = undefined"
apply(case_tac x)
apply simp_all
apply(rename_tac n', case_tac n', simp)
apply(rename_tac n', case_tac n', simp)
apply(rename_tac n', case_tac n', simp)
apply(rename_tac n', case_tac n', simp)
apply(rename_tac n', case_tac n', simp)
apply(rename_tac n', case_tac n', simp)
apply(rename_tac n', case_tac n', simp)
apply(rename_tac n', case_tac n', simp)
apply(rename_tac n', case_tac n', simp)
apply(rename_tac n', case_tac n', simp)
apply simp
done
termination by lexicographic_order

function int_toString :: "int \<Rightarrow> String.literal list"
where
  "int_toString n = 
  (if n < 0 then STR ''-'' # int_toString (- n)
   else if n < 10 then [digit_toString n ]
   else int_toString (n div 10) @ [digit_toString (n mod 10)])"
by pat_completeness simp
termination by size_change

instantiation int :: toString begin
definition [code]: "toString i = Aux.concat (int_toString i)"
instance proof qed
end

instantiation nat :: toString begin
definition [code]: "toString n = toString (int n)"
instance proof qed
end

instantiation option :: (toString) toString begin
primrec toString_option :: "'a option \<Rightarrow> String.literal" where
  "toString None = STR ''None''"
| "toString (Some a) = Aux.concat [STR ''Some ('', toString a, STR '')'']"
instance proof qed
end

instantiation finfun :: ("{toString, card_UNIV, equal, linorder}", toString) toString begin
definition [code]: 
  "toString (f :: 'a \<Rightarrow>f 'b) = 
   Aux.concat 
     (STR ''('' 
     # toString (finfun_default f) 
     # concat (map (\<lambda>x. [STR '','', toString x, STR ''|->'', toString (f $ x)]) (finfun_to_list f)) 
     @ [STR '')''])"
instance proof qed
end

instantiation word :: (len) toString begin
definition [code]: "toString (w :: 'a word) = toString (sint w)"
instance proof qed
end

instantiation "fun" :: (type, type) toString begin
definition [code]: "toString (f :: 'a \<Rightarrow> 'b) = STR ''fn''"
instance proof qed
end

instantiation val :: (toString) toString begin
fun toString_val :: "('a :: toString) val \<Rightarrow> String.literal"
where
  "toString Unit = STR ''Unit''"
| "toString Null = STR ''Null''"
| "toString (Bool b) = Aux.concat [STR ''Bool '', toString b]"
| "toString (Intg i) = Aux.concat [STR ''Intg '', toString i]"
| "toString (Addr a) = Aux.concat [STR ''Addr '', toString a]"
instance proof qed
end

instantiation ty :: toString begin
primrec toString_ty :: "ty \<Rightarrow> String.literal"
where
  "toString Void = STR ''Void''"
| "toString Boolean = STR ''Boolean''"
| "toString Integer = STR ''Integer''"
| "toString NT = STR ''NT''"
| "toString (Class C) = Aux.concat [STR ''Class '', toString C]"
| "toString (T\<lfloor>\<rceil>) = Aux.concat [toString T, STR ''[]'']"
instance proof qed
end

instantiation bop :: toString begin
primrec toString_bop :: "bop \<Rightarrow> String.literal" where
  "toString Eq = STR ''==''"
| "toString NotEq = STR ''!=''"
| "toString LessThan = STR ''<''"
| "toString LessOrEqual = STR ''<=''"
| "toString GreaterThan = STR ''>''"
| "toString GreaterOrEqual = STR ''>=''"
| "toString Add = STR ''+''"
| "toString Subtract = STR ''-''"
| "toString Mult = STR ''*''"
| "toString Div = STR ''/''"
| "toString Mod = STR ''%''"
| "toString BinAnd = STR ''&''"
| "toString BinOr = STR ''|''"
| "toString BinXor = STR ''^''"
| "toString ShiftLeft = STR ''<<''"
| "toString ShiftRightZeros = STR ''>>''"
| "toString ShiftRightSigned = STR ''>>>''"
instance proof qed
end

instantiation addr_loc :: toString begin
primrec toString_addr_loc :: "addr_loc \<Rightarrow> String.literal" where
  "toString (CField C F) = Aux.concat [STR ''CField '', F, STR ''{'', C, STR ''}'']"
| "toString (ACell n) = Aux.concat [STR ''ACell '', toString n]"
instance proof qed
end

instantiation htype :: toString begin
fun toString_htype :: "htype \<Rightarrow> String.literal" where
  "toString (Class_type C) = C"
| "toString (Array_type T n) = Aux.concat [toString T, STR ''['', toString n, STR '']'']"
instance proof qed
end

instantiation obs_event :: (toString, toString) toString begin
primrec toString_obs_event :: "('a :: toString, 'b :: toString) obs_event \<Rightarrow> String.literal"
where
  "toString (ExternalCall ad M vs v) = 
   Aux.concat [STR ''ExternalCall '', M, STR ''('', toString vs, STR '') = '', toString v]"
| "toString (ReadMem ad al v) =
   Aux.concat [STR ''ReadMem '', toString ad, STR ''@'', toString al, STR ''='', toString v]"
| "toString (WriteMem ad al v) =
   Aux.concat [STR ''WriteMem '', toString ad, STR ''@'', toString al, STR ''='', toString v]"
| "toString (NewHeapElem ad hT) = Aux.concat [STR ''Allocate '', toString ad, STR '':'', toString hT]"
| "toString (ThreadStart t) = Aux.concat [STR ''ThreadStart '', toString t]"
| "toString (ThreadJoin t) = Aux.concat [STR ''ThreadJoin '', toString t]"
| "toString (SyncLock ad) = Aux.concat [STR ''SyncLock '', toString ad]"
| "toString (SyncUnlock ad) = Aux.concat [STR ''SyncUnlock '', toString ad]"
| "toString (ObsInterrupt t) = Aux.concat [STR ''Interrupt '', toString t]"
| "toString (ObsInterrupted t) = Aux.concat [STR ''Interrupted '', toString t]"
instance proof qed
end

instantiation prod :: (toString, toString) toString begin
definition "toString = (\<lambda>(a, b). Aux.concat [STR ''('', toString a, STR '', '', toString b, STR '')''])"
instance proof qed
end

instantiation fmod_ext :: (toString) toString begin
definition "toString fd = Aux.concat [STR ''{|volatile='', toString (volatile fd), STR '', '', toString (fmod.more fd), STR ''|}'']"
instance proof qed
end

instantiation unit :: toString begin
definition "toString (u :: unit) = STR ''()''"
instance proof qed
end

instantiation exp :: (toString, toString, toString) toString begin
fun toString_exp :: "('a :: toString, 'b :: toString, 'c :: toString) exp \<Rightarrow> String.literal"
where
  "toString (new C) = Aux.concat [STR ''new '', C]"
| "toString (newArray T e) = Aux.concat [STR ''new '', toString T, STR ''['', toString e, STR '']'']"
| "toString (Cast T e) = Aux.concat [STR ''('', toString T, STR '') ('', toString e, STR '')'']"
| "toString (InstanceOf e T) = Aux.concat [STR ''('', toString e, STR '') instanceof '', toString T]"
| "toString (Val v) = Aux.concat [STR ''Val ('', toString v, STR '')'']"
| "toString (e1 \<guillemotleft>bop\<guillemotright> e2) = Aux.concat [STR ''('', toString e1, STR '') '', toString bop, STR '' ('', toString e2, STR '')'']"
| "toString (Var V) = Aux.concat [STR ''Var '', toString V]"
| "toString (V := e) = Aux.concat [toString V, STR '' := ('', toString e, STR '')'']"
| "toString (AAcc a i) = Aux.concat [STR ''('', toString a, STR '')['', toString i, STR '']'']"
| "toString (AAss a i e) = Aux.concat [STR ''('', toString a, STR '')['', toString i, STR ''] := ('', toString e, STR '')'']"
| "toString (ALen a) = Aux.concat [STR ''('', toString a, STR '').length'']"
| "toString (FAcc e F D) = Aux.concat [STR ''('', toString e, STR '').'', F, STR ''{'', D, STR ''}'']"
| "toString (FAss e F D e') = Aux.concat [STR ''('', toString e, STR '').'', F, STR ''{'', D, STR ''} := ('', toString e', STR '')'']"
| "toString (Call e M es) = Aux.concat ([STR ''('', toString e, STR '').'', M, STR ''(''] @ map toString es @ [STR '')''])"
| "toString (Block V T vo e) = Aux.concat ([STR ''{'', toString V, STR '':'', toString T] @ (case vo of None \<Rightarrow> [] | Some v \<Rightarrow> [STR ''='', toString v]) @ [STR ''; '', toString e, STR ''}''])"
| "toString (Synchronized V e e') = Aux.concat [STR ''synchronized_'', toString V, STR ''_('', toString e, STR '') {'', toString e', STR ''}'']"
| "toString (InSynchronized V ad e) = Aux.concat [STR ''insynchronized_'', toString V, STR ''_('', toString ad, STR '') {'', toString e, STR ''}'']"
| "toString (e;;e') = Aux.concat [toString e, STR ''; '', toString e']"
| "toString (if (e) e' else e'') = Aux.concat [STR ''if ('', toString e, STR '') { '', toString e', STR '' } else { '', toString e'', STR ''}'']"
| "toString (while (e) e') = Aux.concat [STR ''while ('', toString e, STR '') { '', toString e', STR '' }'']"
| "toString (throw e) = Aux.concat [STR ''throw ('', toString e, STR '')'']"
| "toString (try e catch(C V) e') = Aux.concat [STR ''try { '', toString e, STR '' } catch ('', C, STR '' '', toString V, STR '') { '', toString e', STR '' }'']"
instance proof qed
end

instantiation instr :: (toString) toString begin
primrec toString_instr :: "'a instr \<Rightarrow> String.literal" where
  "toString (Load i) = Aux.concat [STR ''Load ('', toString i, STR '')'']"
| "toString (Store i) = Aux.concat [STR ''Store ('', toString i, STR '')'']"
| "toString (Push v) = Aux.concat [STR ''Push ('', toString v, STR '')'']"
| "toString (New C) = Aux.concat [STR ''New '', toString C]"
| "toString (NewArray T) = Aux.concat [STR ''NewArray '', toString T]"
| "toString ALoad = STR ''ALoad''"
| "toString AStore = STR ''AStore''"
| "toString ALength = STR ''ALength''"
| "toString (Getfield F D) = Aux.concat [STR ''Getfield  '', toString F, STR '' '', toString D]"
| "toString (Putfield F D) = Aux.concat [STR ''Putfield  '', toString F, STR '' '', toString D]"
| "toString (Checkcast T) = Aux.concat [STR ''Checkcast '', toString T]"
| "toString (Instanceof T) = Aux.concat [STR ''Instanceof '', toString T]"
| "toString (Invoke M n) =  Aux.concat [STR ''Invoke '', toString M, STR '' '', toString n]"
| "toString Return = STR ''Return''"
| "toString Pop = STR ''Pop''"
| "toString Dup = STR ''Dup''"
| "toString Swap = STR ''Swap''"
| "toString (BinOpInstr bop) = Aux.concat [STR ''BinOpInstr  '', toString bop]"
| "toString (Goto i) = Aux.concat [STR ''Goto '', toString i]"
| "toString (IfFalse i) = Aux.concat [STR ''IfFalse '', toString i]"
| "toString ThrowExc = STR ''ThrowExc''"
| "toString MEnter = STR ''monitorenter''"
| "toString MExit = STR ''monitorexit''"
instance proof qed
end

instantiation trie :: (toString, toString) toString begin
definition [code]: "toString (t :: ('a, 'b) trie) = toString (tm_to_list t)"
instance proof qed
end

instantiation rbt :: ("{toString,linorder}", toString) toString begin
definition [code]: 
  "toString (t :: ('a, 'b) rbt) = 
   Aux.concat (list_toString (STR [Char Nibble2 NibbleC, Char Nibble0 NibbleA]) (rm_to_list t))"
instance proof qed
end

instantiation assoc_list :: (toString, toString) toString begin
definition [code]: "toString = toString \<circ> Assoc_List.impl_of"
instance proof qed
end

code_instance String.literal :: toString (Haskell -)

end