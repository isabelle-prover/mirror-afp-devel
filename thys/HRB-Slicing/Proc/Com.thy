chapter {* Instantiating the Framework with a simple While-Language using procedures *}

section {* Commands *}

theory Com imports "../StaticInter/BasicDefs" begin

subsection {* Variables and Values *}

type_synonym vname = string -- "names for variables"
type_synonym pname = string -- "names for procedures"

datatype val
  = Bool bool      -- "Boolean value"
  | Intg int       -- "integer value" 

abbreviation "true == Bool True"
abbreviation "false == Bool False"


subsection {* Expressions *}

datatype bop = Eq | And | Less | Add | Sub     -- "names of binary operations"

datatype expr
  = Val val                                          -- "value"
  | Var vname                                        -- "local variable"
  | BinOp expr bop expr    ("_ \<guillemotleft>_\<guillemotright> _" [80,0,81] 80)  -- "binary operation"


fun binop :: "bop \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val option"
where "binop Eq v\<^sub>1 v\<^sub>2               = Some(Bool(v\<^sub>1 = v\<^sub>2))"
  | "binop And (Bool b\<^sub>1) (Bool b\<^sub>2)  = Some(Bool(b\<^sub>1 \<and> b\<^sub>2))"
  | "binop Less (Intg i\<^sub>1) (Intg i\<^sub>2) = Some(Bool(i\<^sub>1 < i\<^sub>2))"
  | "binop Add (Intg i\<^sub>1) (Intg i\<^sub>2)  = Some(Intg(i\<^sub>1 + i\<^sub>2))"
  | "binop Sub (Intg i\<^sub>1) (Intg i\<^sub>2)  = Some(Intg(i\<^sub>1 - i\<^sub>2))"
  | "binop bop v\<^sub>1 v\<^sub>2                = None"


subsection {* Commands *}

datatype cmd
  = Skip
  | LAss vname expr        ("_:=_" [70,70] 70)  -- "local assignment"
  | Seq cmd cmd            ("_;;/ _" [60,61] 60)
  | Cond expr cmd cmd      ("if '(_') _/ else _" [80,79,79] 70)
  | While expr cmd         ("while '(_') _" [80,79] 70)
  | Call pname "expr list" "vname list" 
    --"Call needs procedure, actual parameters and variables for return values"



fun num_inner_nodes :: "cmd \<Rightarrow> nat" ("#:_")
where "#:Skip              = 1"
  | "#:(V:=e)              = 2"       (* additional Skip node *)
  | "#:(c\<^sub>1;;c\<^sub>2)            = #:c\<^sub>1 + #:c\<^sub>2"
  | "#:(if (b) c\<^sub>1 else c\<^sub>2) = #:c\<^sub>1 + #:c\<^sub>2 + 1"
  | "#:(while (b) c)       = #:c + 2" (* additional Skip node *)
  | "#:(Call p es rets)    = 2"       (* additional Skip (=Return) node *)


lemma num_inner_nodes_gr_0 [simp]:"#:c > 0"
by(induct c) auto

lemma [dest]:"#:c = 0 \<Longrightarrow> False"
by(induct c) auto


end
