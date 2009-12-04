header {* \isachapter{Instantiating the Framework with a simple While-Language}
  \isaheader{Commands} *}

theory Com imports Main begin

section {* Variables and Values *}

types vname = string -- "names for variables"

datatype val
  = Bool bool      -- "Boolean value"
  | Intg int       -- "integer value" 

abbreviation "true == Bool True"
abbreviation "false == Bool False"

section {* Expressions and Commands*}

datatype bop = Eq | And | Less | Add | Sub     -- "names of binary operations"

datatype expr
  = Val val                                          -- "value"
  | Var vname                                        -- "local variable"
  | BinOp expr bop expr    ("_ \<guillemotleft>_\<guillemotright> _" [80,0,81] 80)  -- "binary operation"


fun binop :: "bop \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val option"
where "binop Eq v\<^isub>1 v\<^isub>2               = Some(Bool(v\<^isub>1 = v\<^isub>2))"
  | "binop And (Bool b\<^isub>1) (Bool b\<^isub>2)  = Some(Bool(b\<^isub>1 \<and> b\<^isub>2))"
  | "binop Less (Intg i\<^isub>1) (Intg i\<^isub>2) = Some(Bool(i\<^isub>1 < i\<^isub>2))"
  | "binop Add (Intg i\<^isub>1) (Intg i\<^isub>2)  = Some(Intg(i\<^isub>1 + i\<^isub>2))"
  | "binop Sub (Intg i\<^isub>1) (Intg i\<^isub>2)  = Some(Intg(i\<^isub>1 - i\<^isub>2))"
  | "binop bop v\<^isub>1 v\<^isub>2                = None"


datatype cmd
  = Skip
  | LAss vname expr        ("_:=_" [70,70] 70)  -- "local assignment"
  | Seq cmd cmd            ("_;;/ _" [61,60] 60)
  | Cond expr cmd cmd      ("if '(_') _/ else _" [80,79,79] 70)
  | While expr cmd         ("while '(_') _" [80,79] 70)


fun num_inner_nodes :: "cmd \<Rightarrow> nat" ("#:_")
where "#:Skip              = 1"
  | "#:(V:=e)              = 2"       (* zus√\<currency>tzlicher Skip-Knoten *)
  | "#:(c\<^isub>1;;c\<^isub>2)            = #:c\<^isub>1 + #:c\<^isub>2"
  | "#:(if (b) c\<^isub>1 else c\<^isub>2) = #:c\<^isub>1 + #:c\<^isub>2 + 1"
  | "#:(while (b) c)       = #:c + 2" (* zus√\<currency>tzlicher Skip-Knoten *)
  


lemma num_inner_nodes_gr_0:"#:c > 0"
by(induct c) auto

lemma [dest]:"#:c = 0 \<Longrightarrow> False"
by(induct c) auto

section {* The state *}

types
  state = "vname \<rightharpoonup> val"

fun "interpret" :: "expr \<Rightarrow> state \<Rightarrow> val option"
where Val: "interpret (Val v) s = Some v"
  | Var: "interpret (Var V) s = s V"
  | BinOp: "interpret (e\<^isub>1\<guillemotleft>bop\<guillemotright>e\<^isub>2) s = 
    (case interpret e\<^isub>1 s of None \<Rightarrow> None
                         | Some v\<^isub>1 \<Rightarrow> (case interpret e\<^isub>2 s of None \<Rightarrow> None
                                                           | Some v\<^isub>2 \<Rightarrow> (
      case binop bop v\<^isub>1 v\<^isub>2 of None \<Rightarrow> None | Some v \<Rightarrow> Some v)))"

end
