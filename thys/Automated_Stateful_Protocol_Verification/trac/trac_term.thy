(*  Title:      trac_term.thy
    Author:     Andreas Viktor Hess, DTU
    Author:     Sebastian A. Mödersheim, DTU
    Author:     Achim D. Brucker, University of Exeter
    Author:     Anders Schlichtkrull, DTU
    SPDX-License-Identifier: BSD-3-Clause
*)

section \<open>Abstract Syntax for Trac Terms\<close>
theory
  trac_term
  imports
    "First_Order_Terms.Term"
    "ml_yacc_lib"
    (* Alternatively (provides, as a side-effect,  ml-yacc-lib):
      "HOL-TPTP.TPTP_Parser" 
    *)
begin
ML\<open>
structure Trac_Utils = 
struct
  val valN = "val"
  val timpliesN = "timplies"
  val occursN = "occurs"
  val enumN = "enum"
  val enum_trac_typeN = "enum"
  val value_trac_typeN = "value"
  val priv_fun_secN = "PrivFunSec"
  val secret_typeN = "SecretType"
  val enum_typeN = "EnumType"
  val other_pubconsts_typeN = "PubConstType"

  val default_extra_types = [enum_typeN, secret_typeN]
  val extended_extra_types = default_extra_types@[other_pubconsts_typeN]
  val all_special_types = value_trac_typeN::enum_trac_typeN::extended_extra_types

  val special_funs = ["occurs", "zero", valN, priv_fun_secN]

  fun infenumN e = enumN^"_"^e

  fun list_find p ts =
    let
      fun aux _ [] = NONE
        | aux n (t::ts) =
            if p t
            then SOME (t,n)
            else aux (n+1) ts
    in
      aux 0 ts
    end
  
  fun map_prod f (a,b) = (f a, f b)
  
  fun list_product [] = [[]]
    | list_product (xs::xss) =
        List.concat (map (fn x => map (fn ys => x::ys) (list_product xss)) xs)
  
  fun list_triangle_product _ [] = []
    | list_triangle_product f (x::xs) = map (f x) xs@list_triangle_product f xs
  
  fun list_subseqs [] = [[]]
    | list_subseqs (x::xs) = let val xss = list_subseqs xs in map (cons x) xss@xss end
  
  fun list_intersect xs ys =
      List.exists (fn x => member (op =) ys x) xs orelse
      List.exists (fn y => member (op =) xs y) ys
  
  fun list_partitions xs constrs =
    let
      val peq = eq_set (op =)
      val pseq = eq_set peq
      val psseq = eq_set pseq
  
      fun illegal p q =
        let
          val pq = union (op =) p q
          fun f (a,b) = member (op =) pq a andalso member (op =) pq b
        in
          List.exists f constrs
        end
  
      fun merges _ [] = []
        | merges q (p::ps) =
            if illegal p q then map (cons p) (merges q ps)
            else (union (op =) p q::ps)::(map (cons p) (merges q ps))
  
      fun merges_all [] = []
        | merges_all (p::ps) = merges p ps@map (cons p) (merges_all ps)
  
      fun step pss = fold (union pseq) (map merges_all pss) []
  
      fun loop pss pssprev =
        let val pss' = step pss
        in if psseq (pss,pss') then pssprev else loop pss' (union pseq pss' pssprev)
        end
  
      val init = [map single xs]
    in
      loop init init
    end

  fun list_rm_pair sel l x = filter (fn e => sel e <> x) l
  
  fun list_minus list_rm l m = List.foldl (fn (a,b) => list_rm b a) l m

  fun list_upto n =
    let
      fun aux m = if m >= n then [] else m::aux (m+1)
    in
      aux 0
    end
end
\<close>

ML\<open>
structure Trac_Term (* : TRAC_TERM *) =
struct
open Trac_Utils
exception TypeError

type TypeDecl = string * string

datatype MsgType = TAtom of string
                 | TComp of string * MsgType list

type TypedVars = (string list * MsgType) list

datatype Msg = Var of string
             | Const of string
             | Fun of string * Msg list
             | Abbrev of string * Msg list
             | Attack

(* TODO: maybe add a set-type *)
datatype cType = Enumeration of string
               | InfiniteEnumeration of string
               | EnumType
               | ValueType
               | PrivFunSecType
               | AtomicType of string
               | ComposedType of string * cType list
               | Untyped

datatype cMsg = cVar of string * cType
              | cConst of string
              | cFun of string * cMsg list
              | cAttack
              | cSet of string * cMsg list
              | cAbs of (string * string list) list
              | cOccursFact of cMsg
              | cPrivFunSec
              | cEnum of string

fun MsgType_str (TAtom a) = a
  | MsgType_str (TComp (f,ts)) = f ^ "(" ^ String.concatWith "," (map MsgType_str ts) ^  ")"

fun Msg_str (Var x) = x
  | Msg_str (Const x) = x
  | Msg_str (Fun (f,ps)) =
      if ps = [] then f else f ^ "(" ^ String.concatWith "," (map Msg_str ps) ^ ")"
  | Msg_str (Abbrev (f,ps)) =
      if ps = [] then f else f ^ "![" ^ String.concatWith "," (map Msg_str ps) ^ "]"
  | Msg_str Attack = "attack"

fun msg_vars t =
  let fun f (Var x) = [x]
        | f (Fun (_,ps)) = List.concat (map f ps)
        | f (Abbrev (_,ps)) = List.concat (map f ps)
        | f (Const _) = []
        | f Attack = []
  in distinct (op =) (f t)
  end

fun cType_str (Enumeration e)         = e
  | cType_str (InfiniteEnumeration e) = e
  | cType_str EnumType                = enum_trac_typeN
  | cType_str ValueType               = value_trac_typeN
  | cType_str PrivFunSecType          = secret_typeN
  | cType_str (AtomicType a)          = a
  | cType_str (ComposedType (f,ts))   = f ^ "(" ^ String.concatWith "," (map cType_str ts) ^ ")"
  | cType_str Untyped                 = "untyped"

fun cMsg_str' notypes (cVar (x,tau)) = x ^ (if notypes then "" else ":" ^ cType_str tau)
  | cMsg_str' _       (cConst s) = s
  | cMsg_str' notypes (cFun (f,ts)) =
      f ^ "(" ^ String.concatWith "," (map (cMsg_str' notypes) ts) ^ ")"
  | cMsg_str' _       cAttack = "attack"
  | cMsg_str' notypes (cSet (s,ts)) =
      s ^ "(" ^ String.concatWith "," (map (cMsg_str' notypes) ts) ^ ")"
  | cMsg_str' _       (cAbs bs) =
      valN ^ "(" ^ String.concatWith ","
        (map (fn (c,cs) => c ^ "(" ^ String.concatWith "," cs  ^ ")") bs) ^
      ")"
  | cMsg_str' notypes (cOccursFact t) = occursN ^ "(" ^ cMsg_str' notypes t ^ ")"
  | cMsg_str' _       cPrivFunSec = priv_fun_secN
  | cMsg_str' _       (cEnum e) = e

val cMsg_str = cMsg_str' false

fun subst_apply_cMsg' (delta:(string * cType) -> cMsg) (t:cMsg) =
  case t of
    cVar x => delta x
  | cFun (f,ts) => cFun (f, map (subst_apply_cMsg' delta) ts)
  | cSet (s,ts) => cSet (s, map (subst_apply_cMsg' delta) ts)
  | cOccursFact bs => cOccursFact (subst_apply_cMsg' delta bs)
  | c => c

fun subst_apply_cMsg (delta:(string * cMsg) list) =
  subst_apply_cMsg' (fn (n,tau) => (
      case List.find (fn x => fst x = n) delta of
        SOME x => snd x
      | NONE => cVar (n,tau)))

fun subst_apply_Msg d (Var x) = (
      case List.find (fn (y,_) => x = y) d of
        SOME (_,t) => t
      | NONE => error ("Error: Cannot find variable " ^ x))
  | subst_apply_Msg _ (Const c) = Const c
  | subst_apply_Msg d (Fun (f,ts')) = Fun (f,map (subst_apply_Msg d) ts')
  | subst_apply_Msg d (Abbrev (f,ts')) = Abbrev (f,map (subst_apply_Msg d) ts')
  | subst_apply_Msg _ Attack = Attack

fun certifyMsgType' finite_enums infinite_enums (TAtom a) =
      if a = enum_trac_typeN then EnumType
      else if a = value_trac_typeN then ValueType
      else if List.exists (fn b => a = b) finite_enums then Enumeration a
      else if List.exists (fn b => a = b) infinite_enums then InfiniteEnumeration a
      else AtomicType a
  | certifyMsgType' finite_enums infinite_enums (TComp (f,ts)) =
      ComposedType (f,map (certifyMsgType' finite_enums infinite_enums) ts)

fun certifyMsgType ((finite_enums:string list)
                    ,(infinite_enums:string list)
                    ,(decls:TypedVars)
                    ,(fresh:TypedVars)) n =
  case List.find (fn (vs,_) => member (op =) vs n) decls of
    SOME (_,tau) => certifyMsgType' finite_enums infinite_enums tau
  | NONE => (
      case List.find (fn (vs,_) => member (op =) vs n) fresh of
        SOME (_,tau) => certifyMsgType' finite_enums infinite_enums tau
      | NONE => error ("Error: Missing or invalid type annotation for variable " ^ n))

fun certifyMsg' notypes params (Var n)         =
      if notypes then cVar (n, Untyped) else cVar (n, certifyMsgType params n)
  | certifyMsg' _       _      (Const c)       =
      cConst c
  | certifyMsg' notypes params (Fun (f,ts))    =
      cFun (f, map (certifyMsg' notypes params) ts)
  | certifyMsg' _       _      (Abbrev p) =
      error ("Error: Got an unexpected term abbreviation (they should have all been expanded " ^
             "and removed at this point): " ^ Msg_str (Abbrev p))
  | certifyMsg' _       _      Attack          =
      cAttack

val certifyMsg = certifyMsg' false
val certifyMsgUntyped = certifyMsg' true ([], [], [], [])

fun mk_Value_cVar x = cVar (x,ValueType)

val fv_Msg =
  let
    fun aux (Var x) = [x]
      | aux (Fun (_,ts)) = List.concat (map aux ts)
      | aux _ = []
  in
    distinct (op =) o aux
  end

val fv_cMsg =
  let
    fun aux (cVar x) = [x]
      | aux (cFun (_,ts)) = List.concat (map aux ts)
      | aux (cSet (_,ts)) = List.concat (map aux ts)
      | aux (cOccursFact bs) = aux bs
      | aux _ = []
  in
    distinct (op =) o aux
  end
end
\<close>

ML\<open>
structure TracProtocol (* : TRAC_TERM *) =
struct
open Trac_Utils Trac_Term

datatype enum_spec_elem =
  Consts of string list
| Union of string list
| InfiniteSet

fun is_Consts t = case t of Consts _ => true | _ => false
fun the_Consts t = case t of Consts cs => cs | _ => error "Consts"

type type_spec = string list
type enum_spec = (string * enum_spec_elem) list
type set_spec_elem  = (string * int * bool)
type set_spec = set_spec_elem list

fun extract_Consts (spec:enum_spec) =
  (List.concat o map the_Consts o filter is_Consts o map snd) spec

type funT = (string * int * MsgType option)
type fun_spec = {private: funT list, public: funT list}

type ruleT = (string * string list) * Msg list * string list
type anaT = ruleT list

datatype prot_label = LabelN | LabelS

type Bvars = TypedVars

datatype Negcheck = INEQ of Msg * Msg
                  | NOTIN of Msg * (string * Msg list)

datatype action = RECEIVE of Msg list
                | SEND of Msg list
                | EQUATION of Msg * Msg
                | LETBINDING of Msg * Msg
                | IN of Msg * (string * Msg list)
                | NOTINANY of Msg * string
                | NEGCHECKS of Bvars * Negcheck list
                | INSERT of Msg * (string * Msg list)
                | DELETE of Msg * (string * Msg list)
                | NEW of TypedVars
                | ATTACK

datatype labeled_action =
  LABELED_ACTION of prot_label * action
| ABBREVIATION of string * Msg list

type transaction_name = string * (string list * MsgType) list * (string * string) list

type transaction={transaction:transaction_name,actions:labeled_action list}

fun typedvars_str xss =
  let fun f (xs,tau) = String.concatWith "," xs ^ ": " ^ MsgType_str tau
  in String.concatWith ", " (map f xss) end

val action_str =
  let
    fun set_action_str (t,(s,ps)) pre mid =
      pre ^ Msg_str t ^ mid ^ s ^ (
      if ps = [] then "" else "(" ^ String.concatWith "," (map Msg_str ps) ^  ")")
    fun negcheck_str (INEQ (t,t')) = Msg_str t ^ " != " ^ Msg_str t'
      | negcheck_str (NOTIN p)    = set_action_str p "" " notin "
    fun to_str (SEND ts)              = "send " ^ String.concatWith ", " (map Msg_str ts)
      | to_str (RECEIVE ts)           = "receive " ^ String.concatWith ", " (map Msg_str ts)
      | to_str (LETBINDING (t,t'))    = "let " ^ Msg_str t ^ " = " ^ Msg_str t'
      | to_str (EQUATION (t,t'))      = Msg_str t ^ " == " ^ Msg_str t'
      | to_str (IN p)                 = set_action_str p "" " in "
      | to_str (NOTINANY (t,s))       = set_action_str (t,(s,[])) "" " notin " ^ "(_)"
      | to_str (NEGCHECKS (bvars,ns)) = String.concatWith " or " (map negcheck_str ns) ^
                                        (if null bvars then "" else " forall ") ^
                                        typedvars_str bvars
      | to_str (INSERT p)             = set_action_str p "insert " " "
      | to_str (DELETE p)             = set_action_str p "delete " " "
      | to_str (NEW xs)               = "new " ^ typedvars_str xs
      | to_str ATTACK                 = "attack"
  in
    to_str
  end

fun labeled_action_str (LABELED_ACTION (lbl,act)) =
      (case lbl of LabelN => "  " | LabelS => "* ") ^ action_str act
  | labeled_action_str (ABBREVIATION (f,ts)) =
      f ^ "![" ^ String.concatWith "," (map Msg_str ts) ^ "]"

fun typedvars_flatten xss = List.concat (map (fn (xs,tau) => map (fn x => (x,tau)) xs) xss)
fun typedvars_fvs xss = map fst (typedvars_flatten xss)

fun action_fvs (RECEIVE ts)        = distinct (op =) (List.concat (map msg_vars ts))
  | action_fvs (LETBINDING (t,t')) = distinct (op =) (msg_vars t@msg_vars t')
  | action_fvs (EQUATION (t,t'))   = distinct (op =) (msg_vars t@msg_vars t')
  | action_fvs (IN (t,(_,p)))      = distinct (op =) (msg_vars t@List.concat (map msg_vars p))
  | action_fvs (NOTINANY (t,_))    = msg_vars t
  | action_fvs (NEGCHECKS (bvars,ns))  =
      let
        fun f (INEQ (t,t')) = msg_vars t@msg_vars t'
          | f (NOTIN (t,(_,p))) = msg_vars t@List.concat (map msg_vars p)
      in
        filter_out (member (op =) (typedvars_fvs bvars)) (distinct (op =) (List.concat (map f ns)))
      end
  | action_fvs (NEW xs)            = distinct (op =) (typedvars_fvs xs)
  | action_fvs (INSERT (t,(_,p)))  = distinct (op =) (msg_vars t@List.concat (map msg_vars p))
  | action_fvs (DELETE (t,(_,p)))  = distinct (op =) (msg_vars t@List.concat (map msg_vars p))
  | action_fvs (SEND ts)           = distinct (op =) (List.concat (map msg_vars ts))
  | action_fvs ATTACK              = []

fun mkTransaction transaction actions = {transaction=transaction,
                                        actions=actions}:transaction

fun is_RECEIVE a = case a of RECEIVE _ => true | _ => false
fun is_SEND a = case a of SEND _ => true | _ => false
fun is_LETBINDING a = case a of LETBINDING _ => true | _ => false
fun is_EQUATION a = case a of EQUATION _ => true | _ => false
fun is_IN a = case a of IN _ => true | _ => false
fun is_NEGCHECKS a = case a of NEGCHECKS _ => true | _ => false
fun is_NOTINANY a = case a of NOTINANY _ => true | _ => false
fun is_INSERT a = case a of INSERT _ => true | _ => false
fun is_DELETE a = case a of DELETE _ => true | _ => false
fun is_NEW a = case a of NEW _ => true | _ => false
fun is_ATTACK a = case a of ATTACK => true | _ => false

fun the_RECEIVE a = case a of RECEIVE t => t | _ => error "RECEIVE"
fun the_SEND a = case a of SEND t => t | _ => error "SEND"
fun the_LETBINDING a = case a of LETBINDING t => t | _ => error "LETBINDING"
fun the_EQUATION a = case a of EQUATION t => t | _ => error "EQUATION"
fun the_IN a = case a of IN t => t | _ => error "IN"
fun the_NEGCHECKS a = case a of NEGCHECKS t => t | _ => error "NEGCHECKS"
fun the_NOTINANY a = case a of NOTINANY t => t | _ => error "NOTINANY"
fun the_INSERT a = case a of INSERT t => t | _ => error "INSERT"
fun the_DELETE a = case a of DELETE t => t | _ => error "DELETE"
fun the_NEW a = case a of NEW t => t | _ => error "FRESH"

fun maybe_the_RECEIVE a = case a of RECEIVE t => SOME t | _ => NONE
fun maybe_the_SEND a = case a of SEND t => SOME t | _ => NONE
fun maybe_the_LETBINDING a = case a of LETBINDING t => SOME t | _ => NONE
fun maybe_the_EQUATION a = case a of EQUATION t => SOME t | _ => NONE
fun maybe_the_IN a = case a of IN t => SOME t | _ => NONE
fun maybe_the_NEGCHECKS a = case a of NEGCHECKS t => SOME t | _ => NONE
fun maybe_the_NOTINANY a = case a of NOTINANY t => SOME t | _ => NONE
fun maybe_the_INSERT a = case a of INSERT t => SOME t | _ => NONE
fun maybe_the_DELETE a = case a of DELETE t => SOME t | _ => NONE
fun maybe_the_NEW a = case a of NEW t => SOME t | _ => NONE

fun subst_apply_labeled_action d (LABELED_ACTION (lbl,a)) =
      let
        val ap = subst_apply_Msg d
        fun rm_vars_ap ys =
          let val zs = typedvars_fvs ys
          in subst_apply_Msg (filter (fn (x,_) => not (member (op =) zs x)) d) end
        fun ap_negcheck xs (INEQ (t,t')) =
              INEQ (rm_vars_ap xs t, rm_vars_ap xs t')
          | ap_negcheck xs (NOTIN (t,(f,ts))) =
              NOTIN (rm_vars_ap xs t,(f,map (rm_vars_ap xs) ts))
        fun aux (RECEIVE ts)        = RECEIVE (map ap ts)
          | aux (SEND ts)           = SEND (map ap ts)
          | aux (EQUATION (t,t'))   = EQUATION (ap t, ap t')
          | aux (LETBINDING (t,t')) = LETBINDING (ap t, ap t')
          | aux (IN (t,(f,ts)))     = IN (ap t,(f,map ap ts))
          | aux (NOTINANY (t,f))    = NOTINANY (ap t, f)
          | aux (NEGCHECKS (xs,ns)) = NEGCHECKS (xs,map (ap_negcheck xs) ns)
          | aux (INSERT (t,(f,ts))) = INSERT (ap t,(f,map ap ts))
          | aux (DELETE (t,(f,ts))) = DELETE (ap t,(f,map ap ts))
          | aux (NEW p)             = NEW p
          | aux ATTACK              = ATTACK
      in
        LABELED_ACTION (lbl,aux a)
      end
  | subst_apply_labeled_action d (ABBREVIATION (f,ts')) =
      ABBREVIATION (f,map (subst_apply_Msg d) ts')

fun expand_term_abbreviations _       (Var x) = Var x
  | expand_term_abbreviations _       (Const c) = Const c
  | expand_term_abbreviations abbrevs (Fun (f,ts)) =
      Fun (f,map (expand_term_abbreviations abbrevs) ts)
  | expand_term_abbreviations abbrevs (Abbrev (f,ts)) = (
      case List.find (fn ((g,_),_) => f = g) abbrevs of
        SOME ((_,xs),t) =>
          if length xs <> length ts
          then error ("Error: The number of parameters given to the term abbreviation " ^
                      Msg_str (Abbrev(f,ts)) ^ " does not match the number of parameters " ^
                      "in its declaration")
          else
            let val delta = xs ~~ ts
            in expand_term_abbreviations abbrevs (subst_apply_Msg delta t)
            end
      | NONE => error ("Error: Cannot find term abbreviation " ^ f))
  | expand_term_abbreviations _       Attack = Attack

fun expand_term_abbreviations_in_action abbrevs ac =
  let
    val exp = expand_term_abbreviations abbrevs
    fun exp_n (INEQ (t,t')) = INEQ (exp t,exp t')
      | exp_n (NOTIN (t,(s,ts))) = NOTIN (exp t,(s,map exp ts))
  in case ac of
        RECEIVE ts => RECEIVE (map exp ts)
      | SEND ts => SEND (map exp ts)
      | EQUATION (t,t') => EQUATION (exp t, exp t')
      | LETBINDING (t,t') => LETBINDING (exp t, exp t')
      | IN (t,(s,ts)) => IN (exp t,(s,map exp ts))
      | NOTINANY (t,s) => NOTINANY (exp t,s)
      | NEGCHECKS (xs,ns) => NEGCHECKS (xs,map exp_n ns)
      | INSERT (t,(s,ts)) => INSERT (exp t,(s,map exp ts))
      | DELETE (t,(s,ts)) => DELETE (exp t,(s,map exp ts))
      | NEW xs => NEW xs
      | ATTACK => ATTACK
  end

fun expand_action_abbreviations (abbrevs:((string * string list) * labeled_action list) list) =
  let
    fun get abbr = case List.find (fn ((a,_),_) => abbr = a) abbrevs of
        SOME ((_,xs),acs) => (xs,acs)
      | NONE => error ("Error: Action sequence abbreviation " ^ abbr ^ " has not been declared")

    fun expand (abbr,ts) =
      let
        val (xs,acs) = get abbr

        val _ = if length xs <> length ts
                then error ("Error: Action sequence abbreviation " ^ abbr ^ " has been applied " ^
                            "with the wrong number of parameters: Expected " ^
                            Int.toString (length xs) ^ " parameters but got " ^
                            Int.toString (length ts))
                else ()

        val delta = xs ~~ ts
      in expand_action_abbreviations abbrevs (map (subst_apply_labeled_action delta) acs) end
  in
    List.concat o
    map (fn a => case a of LABELED_ACTION p => [p]
                         | ABBREVIATION p => expand p)
  end


datatype abbreviation =
  TermAbbreviation of (string * string list) * Msg
| ActionsAbbreviation of (string * string list) * labeled_action list

type abbreviation_spec = abbreviation list

type protocol = {
  name:string
 ,type_spec:type_spec
 ,enum_spec:enum_spec 
 ,set_spec:set_spec
 ,function_spec:fun_spec option
 ,analysis_spec:anaT
 ,abbreviation_spec:abbreviation_spec
 ,transaction_spec:(string option * transaction list) list
 ,fixed_point: (Msg * (string * string) list) list option
}

exception TypeError

val fun_empty = {
                  public=[] 
                 ,private=[]
                }:fun_spec

fun update_fun_public (fun_spec:fun_spec) public =
    ({public = public
     ,private = #private fun_spec 
    }):fun_spec      

fun update_fun_private (fun_spec:fun_spec) private =
    ({public = #public fun_spec
     ,private = private 
    }):fun_spec      


val empty={
            name=""
           ,type_spec=[]
           ,enum_spec=[]
           ,set_spec=[]
           ,function_spec=NONE
           ,analysis_spec=[]
           ,abbreviation_spec=[]
           ,transaction_spec=[]
           ,fixed_point=NONE
          }:protocol

fun update_name (protocol_spec:protocol) name =
    ({name = name
     ,type_spec = #type_spec protocol_spec
     ,enum_spec = #enum_spec protocol_spec
     ,set_spec = #set_spec protocol_spec
     ,function_spec = #function_spec protocol_spec
     ,analysis_spec = #analysis_spec protocol_spec
     ,abbreviation_spec = #abbreviation_spec protocol_spec
     ,transaction_spec = #transaction_spec protocol_spec
     ,fixed_point = #fixed_point protocol_spec
    }):protocol     
fun update_sets (protocol_spec:protocol) set_spec =
    ({name = #name protocol_spec
     ,type_spec = #type_spec protocol_spec
     ,enum_spec = #enum_spec protocol_spec
     ,set_spec = set_spec
     ,function_spec = #function_spec protocol_spec
     ,analysis_spec = #analysis_spec protocol_spec
     ,abbreviation_spec = #abbreviation_spec protocol_spec
     ,transaction_spec = #transaction_spec protocol_spec
     ,fixed_point = #fixed_point protocol_spec
    }):protocol
fun update_type_spec (protocol_spec:protocol) type_spec =
    ({name = #name protocol_spec
     ,type_spec = type_spec
     ,enum_spec = #enum_spec protocol_spec
     ,set_spec = #set_spec protocol_spec
     ,function_spec = #function_spec protocol_spec
     ,analysis_spec = #analysis_spec protocol_spec
     ,abbreviation_spec = #abbreviation_spec protocol_spec
     ,transaction_spec = #transaction_spec protocol_spec
     ,fixed_point = #fixed_point protocol_spec
    }):protocol
fun update_enum_spec (protocol_spec:protocol) enum_spec =
    ({name = #name protocol_spec
     ,type_spec = #type_spec protocol_spec
     ,enum_spec = enum_spec
     ,set_spec = #set_spec protocol_spec
     ,function_spec = #function_spec protocol_spec
     ,analysis_spec = #analysis_spec protocol_spec
     ,abbreviation_spec = #abbreviation_spec protocol_spec
     ,transaction_spec = #transaction_spec protocol_spec
     ,fixed_point = #fixed_point protocol_spec
    }):protocol
fun update_functions (protocol_spec:protocol) function_spec =
    ({name = #name protocol_spec
     ,type_spec = #type_spec protocol_spec
     ,enum_spec = #enum_spec protocol_spec
     ,set_spec = #set_spec protocol_spec
     ,function_spec = SOME function_spec
     ,analysis_spec = #analysis_spec protocol_spec
     ,abbreviation_spec = #abbreviation_spec protocol_spec
     ,transaction_spec = #transaction_spec protocol_spec
     ,fixed_point = #fixed_point protocol_spec
    }):protocol      
fun update_analysis (protocol_spec:protocol) analysis_spec =
    ({name = #name protocol_spec
     ,type_spec = #type_spec protocol_spec
     ,enum_spec = #enum_spec protocol_spec
     ,set_spec = #set_spec protocol_spec
     ,function_spec = #function_spec protocol_spec
     ,analysis_spec = analysis_spec
     ,abbreviation_spec = #abbreviation_spec protocol_spec
     ,transaction_spec = #transaction_spec protocol_spec
     ,fixed_point = #fixed_point protocol_spec
    }):protocol
fun update_abbreviations (protocol_spec:protocol) abbreviation_spec =
    ({name = #name protocol_spec
     ,type_spec = #type_spec protocol_spec
     ,enum_spec = #enum_spec protocol_spec
     ,set_spec = #set_spec protocol_spec
     ,function_spec = #function_spec protocol_spec
     ,analysis_spec = #analysis_spec protocol_spec
     ,abbreviation_spec = abbreviation_spec
     ,transaction_spec = #transaction_spec protocol_spec
     ,fixed_point = #fixed_point protocol_spec
    }):protocol
fun update_transactions (prot_name:string option) (protocol_spec:protocol) transaction_spec =
    ({name = #name protocol_spec
     ,type_spec = #type_spec protocol_spec
     ,enum_spec = #enum_spec protocol_spec
     ,set_spec = #set_spec protocol_spec
     ,function_spec = #function_spec protocol_spec
     ,analysis_spec = #analysis_spec protocol_spec
     ,abbreviation_spec = #abbreviation_spec protocol_spec
     ,transaction_spec = (prot_name,transaction_spec)::(#transaction_spec protocol_spec)
     ,fixed_point = #fixed_point protocol_spec
    }):protocol
fun update_fixed_point (protocol_spec:protocol) fixed_point =
    ({name = #name protocol_spec
     ,type_spec = #type_spec protocol_spec
     ,enum_spec = #enum_spec protocol_spec
     ,set_spec = #set_spec protocol_spec
     ,function_spec = #function_spec protocol_spec
     ,analysis_spec = #analysis_spec protocol_spec
     ,abbreviation_spec = #abbreviation_spec protocol_spec
     ,transaction_spec = #transaction_spec protocol_spec
     ,fixed_point = fixed_point
    }):protocol

end
\<close>


ML\<open>
structure TracProtocolCert (* : TRAC_TERM *) =
struct
open Trac_Utils Trac_Term TracProtocol

type cBvars = (string * cType) list

datatype cNegCheckVariant = cInequality of cMsg * cMsg
                          | cNotInSet of cMsg * cMsg

datatype cPosCheckVariant = cCheck
                          | cAssignment

datatype cAction = cReceive of cMsg list
                 | cSend of cMsg list
                 | cEquality of cPosCheckVariant * (cMsg * cMsg)
                 | cInSet of cPosCheckVariant * (cMsg * cMsg)
                 | cNotInAny of cMsg * string
                 | cNegChecks of cBvars * cNegCheckVariant list
                 | cInsert of cMsg * cMsg
                 | cDelete of cMsg * cMsg
                 | cNew of (string * cType) list
                 | cAssertAttack

type flat_enum_spec = (string * string list * string list) list
type cFunT = (string * int)
type cConstsT = (string * string option)
type cFunSpec = {public_funs: cFunT list, public_consts: cConstsT list,
                 private_consts: cConstsT list}
type cAnaRule = {head: (string * string list), keys: cMsg list,
                 results: string list, is_priv_fun: bool}
type cAnaSpec = cAnaRule list

type cTransaction_name = string * (string * cType) list * (string * string) list

type cTransaction={
  transaction:cTransaction_name
 ,receive_actions:(prot_label * cAction) list
 ,checksingle_actions:(prot_label * cAction) list
 ,checkall_actions:(prot_label * cAction) list
 ,fresh_actions:(prot_label * cAction) list
 ,update_actions:(prot_label * cAction) list
 ,send_actions:(prot_label * cAction) list
 ,attack_actions:(prot_label * cAction) list}

type cProtocol = {
  name:string
 ,type_spec:type_spec
 ,enum_spec:flat_enum_spec 
 ,set_spec:set_spec
 ,function_spec:cFunSpec option
 ,analysis_spec:cAnaSpec
 ,transaction_spec:(string option * cTransaction list) list
 ,fixed_point: (cMsg list * (string * string list) list list *
                ((string * string list) list * (string * string list) list) list) option
}

fun is_Receive a = case a of cReceive _ => true | _ => false
fun is_Send a = case a of cSend _ => true | _ => false
fun is_Equality a = case a of cEquality _ => true | _ => false
fun is_InSet a = case a of cInSet _ => true | _ => false
fun is_NegChecks a = case a of cNegChecks _ => true | _ => false
fun is_NotInAny a = case a of cNotInAny _ => true | _ => false
fun is_Insert a = case a of cInsert _ => true | _ => false
fun is_Delete a = case a of cDelete _ => true | _ => false
fun is_Fresh a = case a of cNew _ => true | _ => false
fun is_Attack a = case a of cAssertAttack => true | _ => false
fun is_Inequality a = case a of cInequality _ => true | _ => false
fun is_NotInSet a = case a of cNotInSet _ => true | _ => false

fun the_Receive a = case a of cReceive t => t | _ => error "Receive"
fun the_Send a = case a of cSend t => t | _ => error "Send"
fun the_Equality a = case a of cEquality t => t | _ => error "Equality"
fun the_InSet a = case a of cInSet t => t | _ => error "InSet"
fun the_NegChecks a = case a of cNegChecks t => t | _ => error "NegChecks"
fun the_NotInAny a = case a of cNotInAny t => t | _ => error "NotInAny"
fun the_Insert a = case a of cInsert t => t | _ => error "Insert"
fun the_Delete a = case a of cDelete t => t | _ => error "Delete"
fun the_Fresh a = case a of cNew ts => ts | _ => error "New"
fun the_Inequality a = case a of cInequality p => p | _ => error "Inequality"
fun the_NotInSet a = case a of cNotInSet p => p | _ => error "NotInSet"

fun maybe_the_Receive a = case a of cReceive t => SOME t | _ => NONE
fun maybe_the_Send a = case a of cSend t => SOME t | _ => NONE
fun maybe_the_Equality a = case a of cEquality (_,t) => SOME t | _ => NONE
fun maybe_the_InSet a = case a of cInSet (_,t) => SOME t | _ => NONE
fun maybe_the_NegChecks a = case a of cNegChecks t => SOME t | _ => NONE
fun maybe_the_NotInAny a = case a of cNotInAny t => SOME t | _ => NONE
fun maybe_the_Insert a = case a of cInsert t => SOME t | _ => NONE
fun maybe_the_Delete a = case a of cDelete t => SOME t | _ => NONE
fun maybe_the_Fresh a = case a of cNew ts => SOME ts | _ => NONE
fun maybe_the_Inequality a = case a of cInequality p => SOME p | _ => NONE
fun maybe_the_NotInSet a = case a of cNotInSet p => SOME p | _ => NONE

fun subst_apply_cAction (delta:(string * cMsg) list) (lbl:prot_label,a:cAction) =
  let
    val ap = subst_apply_cMsg
    val apply = ap delta
    fun rm_vars_apply ys = ap (filter (fn (x,_) => List.all (fn (y,_) => x <> y) ys) delta)
    fun rm_vars_apply_pair xs (t,t') = (rm_vars_apply xs t, rm_vars_apply xs t')
    fun apply_negcheck xs (cInequality p) = cInequality (rm_vars_apply_pair xs p)
      | apply_negcheck xs (cNotInSet p) = cNotInSet (rm_vars_apply_pair xs p)
  in
    case a of
      cReceive ts => (lbl,cReceive (map apply ts))
    | cSend ts => (lbl,cSend (map apply ts))
    | cEquality (v,(t,t')) => (lbl,cEquality (v,(apply t, apply t')))
    | cInSet (v,(x,s)) => (lbl,cInSet (v,(apply x, apply s)))
    | cNotInAny (x,s) => (lbl,cNotInAny (apply x, s))
    | cNegChecks (bvars,ps) => (lbl,cNegChecks (bvars,map (apply_negcheck bvars) ps))
    | cInsert (x,s) => (lbl,cInsert (apply x, apply s))
    | cDelete (x,s) => (lbl,cDelete (apply x, apply s))
    | cNew xs => (lbl,cNew xs)
    | cAssertAttack => (lbl,cAssertAttack)
  end

fun subst_apply_cActions delta =
  map (subst_apply_cAction delta)

val cAction_str =
  let
    val cmsg_str = cMsg_str' true
    fun var_str (x,tau) = x ^ ": " ^ cType_str tau
    fun set_action_str (t,s) pre mid = pre ^ cmsg_str t ^ mid ^ cmsg_str s
    fun negcheck_str (cInequality (t,t')) = cmsg_str t ^ " != " ^ cmsg_str t'
      | negcheck_str (cNotInSet p)        = set_action_str p "" " notin "
    fun to_str (cSend ts)               = "send " ^ String.concatWith ", " (map cmsg_str ts)
      | to_str (cReceive ts)            = "receive " ^ String.concatWith ", " (map cmsg_str ts)
      | to_str (cEquality (psv,(t,t'))) = (
          case psv of
            cCheck => cmsg_str t ^ " == " ^ cmsg_str t'
          | cAssignment => "let " ^ cmsg_str t ^ " = " ^ cmsg_str t')
      | to_str (cInSet (psv,p))    = (
          case psv of
            cCheck => set_action_str p "" " in "
          | cAssignment => set_action_str p "select " " ")
      | to_str (cNotInAny (t,s))        = cmsg_str t ^ " notin " ^ s ^ "(_)"
      | to_str (cNegChecks (bvars,ns))  = String.concatWith " or " (map negcheck_str ns) ^
                                          (if null bvars then "" else " forall ") ^
                                          String.concatWith ", " (map var_str bvars)
      | to_str (cInsert p)              = set_action_str p "insert " " "
      | to_str (cDelete p)              = set_action_str p "delete " " "
      | to_str (cNew xs)                = "new " ^ String.concatWith ", " (map var_str xs)
      | to_str cAssertAttack            = "attack"
  in
    to_str
  end

fun cTransaction_str (tr:cTransaction) =
  let
    fun lbl_act_str (lbl,act) = (case lbl of LabelN => "  " | LabelS => "* ") ^ cAction_str act
    fun name_str (name, decls, ineqs) =
      name ^ "(" ^ String.concatWith ", " (map (fn (x,t) => x ^ ": " ^ cType_str t) decls) ^ ")" ^
      (if null ineqs then "" else " where ") ^
      String.concatWith ", " (map (fn (a,b) => a ^ " != " ^ b) ineqs)
  in
    name_str (#transaction tr) ^ "\n" ^
    String.concatWith "\n" (
      map lbl_act_str
        ((#receive_actions tr)
        @(#checksingle_actions tr)
        @(#checkall_actions tr)
        @(#fresh_actions tr)
        @(#update_actions tr)
        @(#send_actions tr)
        @(#attack_actions tr))) ^
    "."
  end

fun is_priv_fun_trac (trac:TracProtocol.protocol) f =
  let val funs = #private (Option.valOf (#function_spec trac))
  in List.exists (fn (g,n,_) => f = g andalso n <> 0) funs end

fun get_enum_consts_trac (trac:TracProtocol.protocol) =
  distinct (op =) (TracProtocol.extract_Consts (#enum_spec trac))

fun flatten_enum_spec_trac (trac:TracProtocol.protocol) =
  let
    open TracProtocol
    fun step taus (s,e) =
      case e of
        Union es =>
          let
            fun f e = case List.find (fn (a,_) => e = a) taus of
                        SOME (_,Union es') =>
                          let
                            val _ = if List.exists (fn a => e = a) es'
                                    then error ("Error: There is a cyclic dependency for " ^
                                                "enumeration " ^ e)
                                    else ()
                          in es' end
                      | SOME _ => [e]
                      | NONE => error ("Error: Enumeration " ^ e ^ " has not been declared")
          in
            (s,Union (distinct (op =) (List.concat (map f es))))
          end
      | c => (s,c)
    fun loop taus =
      let
        val taus' = map (step taus) taus
      in
        if taus = taus'
        then taus
        else loop taus'
      end
    fun postproc _    (e,InfiniteSet) = (e,[],[e])
      | postproc _    (e,Consts cs)   = (e,distinct (op =) cs,[])
      | postproc spec (e,Union es)    =
          let
            fun get e' = case List.find (fn (x,_) => x = e') spec of
                SOME p => p
              | NONE => error ("Error: Enumeration " ^ e ^ " has not been declared")
            fun ins (_,Consts cs) (fes,ies) = (distinct (op =) (fes@cs),ies)
              | ins (e',InfiniteSet) (fes,ies) = (fes,distinct (op =) (ies@[e']))
              | ins _ _ = error "Error: Couldn't flatten the enumerations"
            val (fes,ies) = fold (ins o get) es ([],[])
          in (e,fes,ies) end
    val flat_enum_spec = loop (#enum_spec trac)
  in
    map (postproc flat_enum_spec) flat_enum_spec
  end

fun flatten_finite_enum_spec_trac (trac:TracProtocol.protocol) =
  map_filter (fn (e,cs,es) => if null es then SOME (e,cs) else NONE) (flatten_enum_spec_trac trac)

fun priv_fun_type_enc trac (Trac_Term.ComposedType (f,ts)) =
      if is_priv_fun_trac trac f andalso
         (case ts of Trac_Term.PrivFunSecType::_ => false | _ => true)
      then Trac_Term.ComposedType (f,Trac_Term.PrivFunSecType::map (priv_fun_type_enc trac) ts)
      else Trac_Term.ComposedType (f,map (priv_fun_type_enc trac) ts)
  | priv_fun_type_enc _ tau = tau

fun priv_fun_enc trac t =
  let
    open Trac_Term

    fun aux constr f ts =
      if is_priv_fun_trac trac f andalso
         (case ts of cPrivFunSec::_ => false | _ => true)
      then constr (f,cPrivFunSec::map (priv_fun_enc trac) ts)
      else constr (f,map (priv_fun_enc trac) ts)
  in
    case t of
      cVar (x,tau) => cVar (x, priv_fun_type_enc trac tau)
    | cFun (f,ts) => aux cFun f ts
    | cSet (s,ts) => aux cSet s ts
    | _ => t
  end

fun transform_cMsg trac =
  let
    open Trac_Term

    fun conv_enum_consts trac (t:cMsg) = 
      let
        val enums = get_enum_consts_trac trac
        fun aux (cFun (f,ts)) =
              if List.exists (fn x => x = f) enums
              then if null ts
                   then cEnum f
                   else error ("Error: Enumeration constant " ^ f ^
                               " should not have a parameter list")
              else
                cFun (f,map aux ts)
          | aux (cConst c) =
              if List.exists (fn x => x = c) enums
              then cEnum c
              else cConst c
          | aux (cSet (s,ts)) = cSet (s,map aux ts)
          | aux (cOccursFact bs) = cOccursFact (aux bs)
          | aux t = t
      in
        aux t
      end
    
    fun val_to_abs (t:cMsg) =
      let
        fun aux t = case t of cEnum b => b | _ => error "Error: Invalid val parameter list"
    
        fun val_to_abs_list [] = []
          | val_to_abs_list (cConst "0"::ts) = val_to_abs_list ts
          | val_to_abs_list (cFun (s,ps)::ts) = (s, map aux ps)::val_to_abs_list ts
          | val_to_abs_list (cSet (s,ps)::ts) = (s, map aux ps)::val_to_abs_list ts
          | val_to_abs_list ts = error ("Error: Invalid val parameter list: [" ^
                                      String.concatWith ", " (map cMsg_str ts) ^ "]")
      in
        case t of
          cFun (f,ts) =>
            if f = valN
            then cAbs (val_to_abs_list ts)
            else cFun (f,map val_to_abs ts)
        | cSet (s,ts) =>
            cSet (s,map val_to_abs ts)
        | cOccursFact bs =>
            cOccursFact (val_to_abs bs)
        | t => t
      end
    
    fun occurs_enc t =
      let
        fun aux [cVar x] = cVar x
          | aux [cAbs bs] = cAbs bs
          | aux ts = error ("Error: Invalid occurs parameter list: [" ^
                            String.concatWith ", " (map cMsg_str ts) ^ "]")
        fun enc (cFun (f,ts)) = (
              if f = occursN
              then cOccursFact (aux ts)
              else cFun (f,map enc ts))
          | enc (cSet (s,ts)) =
              cSet (s,map enc ts)
          | enc (cOccursFact bs) =
              cOccursFact (enc bs)
          | enc t = t
      in
        enc t
      end
  in
    occurs_enc o val_to_abs o conv_enum_consts trac o priv_fun_enc trac
  end

fun certify_fixpoint trac fp =
  let
    open Trac_Term

    fun mk_enum_substs (vars:(string * cType) list) =
      let
        val flat_enum_spec = flatten_finite_enum_spec_trac trac
        val deltas =
          let
            fun f (s,Enumeration tau) = (
                case List.find (fn x => fst x = tau) flat_enum_spec of
                  SOME x => map (fn c => (s,c)) (snd x)
                | NONE => error ("Error: Enumeration " ^ tau ^
                                 " was not found in the finite enumeration specification"))
              | f (s,_) = error ("Error: Variable " ^ s ^ " is not of finite enumeration type")
          in
            list_product (map f vars)
          end
      in
        map (fn d => map (fn (x,t) => (x,cEnum t)) d) deltas
      end

    fun ground_enum_variables (fp:cMsg list) =
      let
        fun do_grounding t = map (fn d => subst_apply_cMsg d t) (mk_enum_substs (fv_cMsg t))
      in
        List.concat (map do_grounding fp)
      end

    fun split_fp (fp:cMsg list) =
      let
        fun fa t = case t of cFun (s,_) => s <> timpliesN | _ => true
        fun fb (t,ts) = case t of cOccursFact (cAbs bs) => bs::ts | _ => ts
        fun fc (cFun (s, [cAbs bs, cAbs cs]),ts) =
            if s = timpliesN
            then (bs,cs)::ts
            else ts
          | fc (_,ts) = ts
  
        val eq = eq_set (op =)
        fun eq_pairs ((a,b),(c,d)) = eq (a,c) andalso eq (b,d)
  
        val timplies_trancl =
          let
            fun trans_step ts =
              let
                fun aux (s,t) = map (fn (_,u) => (s,u)) (filter (fn (v,_) => eq (t,v)) ts)
              in
                distinct eq_pairs (filter (not o eq) (ts@List.concat (map aux ts)))
              end
            fun loop ts =
              let
                val ts' = trans_step ts
              in
                if eq_set eq_pairs (ts,ts')
                then ts
                else loop ts'
              end
          in
            loop
          end
  
        val ti = List.foldl fc [] fp
      in
        (filter fa fp, distinct eq (List.foldl fb [] fp@map snd ti), timplies_trancl ti)
      end

    fun check_no_vars_and_consts (fp:cMsg list) =
      let
        fun aux (cVar _) = false
          | aux (cConst _) = false
          | aux (cFun (_,ts)) = List.all aux ts
          | aux (cSet (_,ts)) = List.all aux ts
          | aux (cOccursFact bs) = aux bs
          | aux _ = true
      in
        if List.all aux fp
        then fp
        else error ("There shouldn't be any cVars and cConsts at this point in the " ^
                    "fixpoint translation")
      end
  in
    fp |> map (fn (m,t) => certifyMsg (map snd t, [], map (fn (a,b) => ([a],TAtom b)) t, []) m)
       |> ground_enum_variables
       |> map (transform_cMsg trac)
       |> check_no_vars_and_consts
       |> split_fp
  end

fun certifyAction params              (lbl,SEND ts)           = (lbl,cSend
      (map (certifyMsg params) ts))
  | certifyAction params              (lbl,RECEIVE ts)        = (lbl,cReceive
      (map (certifyMsg params) ts))
  | certifyAction params              (lbl,LETBINDING (t,t')) = (lbl,cEquality
      (cAssignment, (certifyMsg params t, certifyMsg params t')))
  | certifyAction params              (lbl,EQUATION (t,t'))   = (lbl,cEquality
      (cCheck, (certifyMsg params t, certifyMsg params t')))
  | certifyAction params              (lbl,IN (x,(s,ps)))     =
      let
        fun f (Enumeration _) = true
          | f (InfiniteEnumeration _) = true
          | f EnumType = true
          | f ValueType = true
          | f _ = false
        val taus = distinct (op =) (map (certifyMsgType params) (action_fvs (IN (x,(s,ps)))))
        val poscheckvariant = cAssignment (* TODO: fix *)
            (* if List.all f taus then cCheck else cAssignment *)
      in
        (lbl,cInSet (poscheckvariant, (certifyMsg params x,
                                       cSet (s, map (certifyMsg params) ps))))
      end
  | certifyAction params              (lbl,NOTINANY (x,s))    = (lbl,cNotInAny
      (certifyMsg params x, s))
  | certifyAction params              (lbl,NEGCHECKS (xs,ns)) = (lbl,cNegChecks
      (map (fn (x,tau) => (x,certifyMsgType' (#1 params) (#2 params) tau)) (typedvars_flatten xs),
       map (fn n => case n of
                      INEQ (t,t') => cInequality (certifyMsg params t,
                                                  certifyMsg params t')
                    | NOTIN (t,(s,ps)) => cNotInSet (certifyMsg params t,
                                                     cSet (s, map (certifyMsg params) ps)))
           ns))
  | certifyAction params              (lbl,INSERT (x,(s,ps))) = (lbl,cInsert
      (certifyMsg params x, cSet (s, map (certifyMsg params) ps)))
  | certifyAction params              (lbl,DELETE (x,(s,ps))) = (lbl,cDelete
      (certifyMsg params x, cSet (s, map (certifyMsg params) ps)))
  | certifyAction (fenums,ienums,_,_) (lbl,NEW xs)            = (lbl,cNew
      (let
        val xs = typedvars_flatten xs
        fun check (TAtom a) =
              if a = enum_trac_typeN
              then error "Error: The special enum type is not allowed in \"new\" actions"
              else if List.exists (fn e => a = e) (fenums@ienums)
              then error "Error: Enumeration annotations are not allowed in \"new\" actions"
              else TAtom a
          | check (TComp _) =
              error "Error: Composed type annotations in \"new\" actions are not allowed"
       in map (fn (x,tau) => (x,certifyMsgType' fenums ienums (check tau))) xs end))
  | certifyAction _                   (lbl,ATTACK)            = (lbl,cAssertAttack)

fun certifyTransactionName fenums ienums ((name, vars, ineqs):transaction_name) =
  let val cert_vars = map (fn x => (x,certifyMsgType (fenums, ienums, vars, []) x))
  in (name, List.concat (map (cert_vars o fst) vars), ineqs) end

fun certifyTransaction finite_enumerations infinite_enumerations (tr:transaction) =
  let
    val tr_acs = map (fn a => case a of
                                LABELED_ACTION p => p
                              | ABBREVIATION p =>
                                  error ("Error: Got an unexpected action sequence abbreviation " ^
                                         "(they should have all been expanded and removed at " ^
                                         "this point): " ^
                                         labeled_action_str (ABBREVIATION p)))
                     (#actions tr)

    val mk_cOccurs = cOccursFact
    fun mk_Value_cVar x = cVar (x,ValueType)
    fun mk_cInequality star_acs_vars x y =
      let val mem = member (op =) star_acs_vars
          val lbl = if mem x andalso mem y then LabelS else LabelN
      in (lbl, cNegChecks ([],[cInequality (mk_Value_cVar x, mk_Value_cVar y)])) end
    fun mk_cInequalities star_acs_vars = list_triangle_product (mk_cInequality star_acs_vars)

    val fresh_vars = List.concat (map_filter (maybe_the_NEW o snd) tr_acs)
    val fresh_vars' = typedvars_flatten fresh_vars
    val fresh_vals = map_filter
      (fn (v,tau) => if tau = TAtom value_trac_typeN then SOME v else NONE)
      fresh_vars'
    val decl_vars = #2 (#transaction tr)
    val decl_vars' = List.concat (map fst decl_vars)
    val neq_constrs = #3 (#transaction tr)
    val bvars = List.concat (map fst (map_filter (maybe_the_NEGCHECKS o snd) tr_acs))

    val _ = if     List.exists (fn x     => List.exists (fn (y,_) => x = y) fresh_vars') decl_vars'
            orelse List.exists (fn (x,_) => List.exists (fn y     => x = y) decl_vars') fresh_vars'
            then error "The fresh and the declared variables must not overlap"
            else ()

    val _ = case List.find (fn (x,y) => x = y) neq_constrs of
              SOME (x,y) => error ("Illegal inequality constraint: " ^ x ^ " != " ^ y)
            | NONE => ()

    val (vars_in_acs, vars_in_star_acs) =
      let val f = distinct (op =) o List.concat o map (action_fvs o snd)
      in (f tr_acs, f (filter (fn (l,_) => l = LabelS) tr_acs)) end
    val nonfresh_vals = List.concat (
      map fst (filter (fn x => snd x = TAtom value_trac_typeN) (#2 (#transaction tr))))
    val (nonfresh_vals_in_acs, nonfresh_vals_in_star_acs) =
      let fun f xs = filter (fn x => member (op =) xs x) nonfresh_vals
      in (f vars_in_acs, f vars_in_star_acs) end
    val enum_vars =
      map_filter (fn (x,tau) => case tau of
                      TAtom e => if List.exists (fn e' => e = e')
                                                (finite_enumerations@infinite_enumerations)
                                 then SOME (x,e) else NONE
                    | TComp _ => NONE)
                 (#2 (#transaction tr))
    val nonenum_decl_vars =
      filter (fn (x,_) => not (List.exists (fn (y,_) => x = y) enum_vars)) decl_vars

    fun lblS t = (LabelS,t)

    val cactions =
      let val xs = decl_vars@bvars
      in map (certifyAction (finite_enumerations, infinite_enumerations, xs, fresh_vars)) tr_acs
      end

    val cname = certifyTransactionName finite_enumerations infinite_enumerations (#transaction tr)

    fun mk_occurs_step f xs =
      if null xs then NONE
      else SOME ((lblS o f o map (mk_cOccurs o mk_Value_cVar)) xs)

    fun is_poscheck1 (_,a) = is_Equality a orelse is_InSet a
    fun is_check1 p = is_poscheck1 p orelse is_NegChecks (snd p)

    val nonfresh_occurs = mk_occurs_step cReceive nonfresh_vals
    val receives = filter (is_Receive o snd) cactions
    val value_inequalities = mk_cInequalities nonfresh_vals_in_star_acs nonfresh_vals_in_acs
    val checksingles = filter is_check1 cactions
    val checkalls = filter (is_NotInAny o snd) cactions
    val updates = filter (fn (_,a) => is_Insert a orelse is_Delete a) cactions
    val fresh = filter (is_Fresh o snd) cactions
    val sends = filter (is_Send o snd) cactions
    val fresh_occurs = mk_occurs_step cSend fresh_vals
    val attack_signals = filter (is_Attack o snd) cactions
  in
    {transaction = cname,
     receive_actions = receives,
(*         case nonfresh_occurs of
          NONE => receives
        | SOME occs => occs::receives, *)
     checksingle_actions = value_inequalities@checksingles,
     checkall_actions = checkalls,
     fresh_actions = fresh,
     update_actions = updates,
     send_actions = sends,
(*         case fresh_occurs of
          NONE => sends
        | SOME occs => case sends of
            ((LabelS, cSend ts)::sends') => (lblS o cSend) ((the_Send o snd) occs@ts)::sends'
          | _ => occs::sends, *)
     attack_actions = attack_signals}:cTransaction
  end

  fun get_finite_enum_spec_trac (trac:protocol) =
    let
      val spec = #enum_spec trac
      val finite_enum_spec =
        let
          fun is_finite e =
            List.exists
              (fn (s,t) => s = e andalso (case t of
                  TracProtocol.Consts _ => true
                | TracProtocol.Union ts => List.all is_finite ts
                | TracProtocol.InfiniteSet => false))
              spec
        in
          filter (is_finite o fst) spec
        end
    in
      finite_enum_spec
    end

  fun get_infinite_enum_spec_trac (trac:protocol) =
    filter_out (member (op =) (get_finite_enum_spec_trac trac)) (#enum_spec trac)

  fun get_finite_enum_names_trac (trac:protocol) =
    map fst (get_finite_enum_spec_trac trac)

  fun get_infinite_enum_names_trac (trac:protocol) =
    map fst (get_infinite_enum_spec_trac trac)

  fun get_enum_names_trac (trac:protocol) =
    map fst (#enum_spec trac)

  fun get_funs_trac (trac:protocol) =
      let
        fun rm_special_funs sel l = list_minus (list_rm_pair sel) l special_funs
        fun append_sec fs = fs@[(priv_fun_secN, 0, NONE)]
        val filter_funs = filter (fn (_,n,_) => n <> 0)
        val filter_consts = filter (fn (_,n,_) => n = 0)
        fun inc_ar (s,n,tau) = (s, 1+n, tau)
      in
        case (#function_spec trac) of 
             NONE => ([],[],[])
           | SOME ({public=pub, private=priv}) =>
              let
                val pub_symbols = rm_special_funs #1 (pub@map inc_ar (filter_funs priv))
                val pub_funs = filter_funs pub_symbols
                val pub_consts = filter_consts pub_symbols
                val priv_consts = append_sec (rm_special_funs #1 (filter_consts priv))
              in
                (pub_funs, pub_consts, priv_consts)
              end
      end


  fun get_term_abbreviations_trac (trac:protocol) =
    map_filter (fn a => case a of TracProtocol.TermAbbreviation t => SOME t | _ => NONE)
               (#abbreviation_spec trac)

  fun get_action_abbreviations_trac (trac:protocol) =
    map_filter (fn a => case a of TracProtocol.ActionsAbbreviation t => SOME t | _ => NONE)
               (#abbreviation_spec trac)

  fun check_for_invalid_trac_specification (trac:TracProtocol.protocol) = let
      open Trac_Term TracProtocol

      datatype action_status =
        Passed | InvalidSetParam | WrongPosition | IllformedVars | InvalidAnnotationNewAction |
        InvalidFunctionSymbols of (string * int) list |
        InvalidSetSymbols of (string * int option) list

      val has_dups = has_duplicates (op =)
      val dups_str = String.concatWith ", " o duplicates (op =)

      val expand_abbrevs =
        expand_action_abbreviations (get_action_abbreviations_trac trac)

      val enumerations = get_enum_names_trac trac
      val finite_enumerations = get_finite_enum_names_trac trac
      val infinite_enumerations = get_infinite_enum_names_trac trac
      val set_names = map #1 (#set_spec trac)
      val set_spec = map (fn (s,n,_) => (s,n)) (#set_spec trac)
      val enum_consts = get_enum_consts_trac trac
      val fun_names = case #function_spec trac of
            SOME fs => map #1 ((#public fs)@(#private fs))
          | NONE => []
      val fun_spec = case #function_spec trac of
            SOME fs => map_filter
                        (fn (s,n,tau) => if n > 0 andalso tau = NONE then SOME (s,n) else NONE)
                        ((#public fs)@(#private fs))
          | NONE => []

      val ana_funs = map (#1 o #1) (#analysis_spec trac)
      val ana_args = map (#2 o #1) (#analysis_spec trac)
      val ana_has_illegal_var_in_body = not o
            (fn ((_,xs),ts,ys) => subset (op =) (ys@List.concat (map Trac_Term.fv_Msg ts), xs))

      val abb_funs = map (fn a => case a of
                                    TermAbbreviation ((f,_),_) => f
                                  | ActionsAbbreviation ((f,_),_) => f)
                         (#abbreviation_spec trac)
      val abb_args = map (fn a => case a of
                                    TermAbbreviation ((_,xs),_) => xs
                                  | ActionsAbbreviation ((_,xs),_) => xs)
                         (#abbreviation_spec trac)
      fun abb_has_illegal_var_in_body (TermAbbreviation ((_,xs),t)) =
            not (subset (op =) (Trac_Term.fv_Msg t, xs))
        | abb_has_illegal_var_in_body (ActionsAbbreviation ((_,xs),acs)) =
            not (subset (op =) (List.concat (map (action_fvs o snd) (expand_abbrevs acs)), xs))

      val trs = List.concat (map snd (#transaction_spec trac))
      val tr_names = map (#1 o #transaction) trs 
      val tr_sec_names = map_filter #1 (#transaction_spec trac)
      val tr_hds =
        map (fn tr => (#1 (#transaction tr), #2 (#transaction tr))) trs
      val tr_acs =
        map (fn tr => (#1 (#transaction tr), #2 (#transaction tr),
                       map snd (expand_abbrevs (#actions tr)))) trs
      val tr_mem_acs_sets =
        let
          val tr_mem_acs = filter (fn a => is_IN a orelse is_NOTINANY a orelse is_NEGCHECKS a)
                                  (List.concat (map #3 tr_acs))
          fun f a =
            case a of
              IN (_,(s,_)) => [s]
            | NOTINANY (_,s) => [s]
            | NEGCHECKS (_,bs) =>
                map_filter (fn b => case b of NOTIN (_,(s,_)) => SOME s | _ => NONE) bs
            | _ => []
          val s = tr_mem_acs |> map f |> List.concat |> distinct (op =)
        in s end

      val illegal_atomic_types = extended_extra_types
      val new_action_illegal_annotations = enumerations@enum_trac_typeN::illegal_atomic_types
      val illegal_composed_type_subterms = enumerations@value_trac_typeN::illegal_atomic_types

      val user_types_overlapping_enums =
        filter (member (op =) (#type_spec trac)) enumerations

      fun value_free_type (TAtom e) = e <> value_trac_typeN
        | value_free_type (TComp (_,ts)) = List.all value_free_type ts

      fun var_decl_has_illegal_type (_,TAtom a) = List.exists (fn b => a = b) illegal_atomic_types
        | var_decl_has_illegal_type (_,TComp ts) =
            let
              val funs =
                case (#function_spec trac) of 
                  NONE => []
                | SOME {private=privs, public=pubs} => pubs@privs

              fun illegal_symbol a = List.exists (fn b => a = b) illegal_composed_type_subterms

              fun wrong_arity a bs =
                null bs orelse List.exists (fn (f,n,_) => f = a andalso length bs <> n) funs

              fun check (TAtom a) = illegal_symbol a
                | check (TComp (s,ts)) =
                    illegal_symbol s orelse wrong_arity s ts orelse List.exists check ts
            in
              check (TComp ts)
            end

      fun no_value_vars_in_decl (tr:transaction) =
        List.all (value_free_type o snd) (#2 (#transaction tr))

      fun no_value_vars_in_decl_and_new_acs (tr:transaction) =
        no_value_vars_in_decl tr andalso
        List.all (List.all (value_free_type o snd))
(* (fn (_,t) => case t of SOME tau => value_free_type tau | _ => false) *)
                 (map_filter (maybe_the_NEW o snd) (expand_abbrevs (#actions tr)))

      fun is_value_init_transaction (tr:transaction) =
        let
          val acs = map snd (expand_abbrevs (#actions tr))
          val priv_funs = case #function_spec trac of SOME fs => map #1 (#private fs) | NONE => []
          val decl = #2 (#transaction tr)
          fun is_not_value_var x =
            List.exists (fn (ys,t) => member (op =) ys x andalso value_free_type t) decl
          fun is_not_priv f = List.all (fn g => f <> g) priv_funs
          fun valid_msg (Var x) = is_not_value_var x
            | valid_msg (Const c) = is_not_priv c
            | valid_msg (Fun (f,ts)) = is_not_priv f andalso List.all valid_msg ts
            | valid_msg (Abbrev _) = false
            | valid_msg Attack = true
          fun NEW_action_with_value_annotations_only a =
            case a of
              NEW xss => List.all (fn (_,t) => t = TAtom value_trac_typeN) xss
            | _ => false
        in
          no_value_vars_in_decl tr andalso
          List.exists NEW_action_with_value_annotations_only acs andalso
          List.all (List.all valid_msg) (map_filter maybe_the_RECEIVE acs) andalso
          List.all (fn a => is_NEW a orelse is_INSERT a orelse is_SEND a) acs andalso
          List.all (fn (_,(s,_)) => not (member (op =) tr_mem_acs_sets s))
                   (map_filter maybe_the_INSERT acs)
        end
      fun value_producing_transactions_requirement tr_secs =
        List.all (List.exists is_value_init_transaction o snd) tr_secs orelse
        List.all (List.all no_value_vars_in_decl_and_new_acs o snd) tr_secs

      fun set_action_enum_params decls ps =
        let
          fun is_enum_var x = List.exists
                (fn (y,t) => x = y andalso List.exists (fn e => t = TAtom e) finite_enumerations)
                decls
        in
          List.all (fn p => case p of
              Var x => is_enum_var x
            | Const c => List.exists (fn b => b = c) enum_consts
            | Fun (c,ps) => ps = [] andalso List.exists (fn b => b = c) enum_consts
            | _ => false) ps
        end

      fun set_action_param_check f ds (INSERT (_,(_,ps))) = f ds ps
        | set_action_param_check f ds (DELETE (_,(_,ps))) = f ds ps
        | set_action_param_check f ds (IN (_,(_,ps))) = f ds ps
        | set_action_param_check f ds (NEGCHECKS (_,ns)) =
            List.all (fn n => case n of NOTIN (_,(_,ps)) => f ds ps | _ => true) ns
        | set_action_param_check _ _ _ = true

      fun wfst' xs [] = xs
        | wfst' xs (a::acs) = case a of
            (RECEIVE ts) => wfst' (distinct (op =) (xs@action_fvs (RECEIVE ts))) acs
          | (LETBINDING (t,_)) => wfst' (distinct (op =) (xs@msg_vars t)) acs
          | (IN p) => wfst' (distinct (op =) (xs@action_fvs (IN p))) acs
          | (NEW ys) => wfst' (xs@typedvars_fvs ys) acs
          | _ => wfst' xs acs

      fun wfstp decl xs prev_fvs insert_send_fvs a = case a of
            (RECEIVE ts) => subset (op =) (action_fvs (RECEIVE ts), decl)
          | (SEND ts) => subset (op =) (action_fvs (SEND ts), xs)
          | (EQUATION p) => subset (op =) (action_fvs (EQUATION p), decl)
          | (LETBINDING (t,t')) =>
              subset (op =) (msg_vars t, decl) andalso
              subset (op =) (msg_vars t', xs)
          | (IN p) => subset (op =) (action_fvs (IN p), decl)
          | (NOTINANY p) => subset (op =) (action_fvs (NOTINANY p), decl)
          | (NEGCHECKS p) => subset (op =) (action_fvs (NEGCHECKS p), decl)
          | (INSERT p) => subset (op =) (action_fvs (INSERT p), xs)
          | (DELETE p) => subset (op =) (action_fvs (DELETE p), decl@xs)
          | (NEW ys) =>
              let val zs = typedvars_fvs ys
              in not (has_dups zs) andalso
                 subset (op =) (zs, insert_send_fvs) andalso
                 List.all (fn y =>
                             not (member (op =) decl y) andalso
                             not (member (op =) prev_fvs y))
                          zs
              end
          | ATTACK => true

      fun wfst decl prev_acs next_acs a =
        let val f = map fst
            fun g (_,tau) = case tau of TAtom ta => member (op =) enumerations ta | _ => true
            val h = List.concat o map action_fvs
            val prev_fvs = h prev_acs
            val insert_send_fvs = h (filter (fn b => is_INSERT b orelse is_SEND b) next_acs)
        in wfstp (f decl) (wfst' (f (filter g decl)) prev_acs) prev_fvs insert_send_fvs a end

      fun action_order_check _        (RECEIVE _) = true
        | action_order_check next_acs (LETBINDING _) = List.all (not o is_RECEIVE) next_acs
        | action_order_check next_acs (EQUATION _) = List.all (not o is_RECEIVE) next_acs
        | action_order_check next_acs (NEGCHECKS _) = List.all (not o is_RECEIVE) next_acs
        | action_order_check next_acs (IN _) = List.all (not o is_RECEIVE) next_acs
        | action_order_check next_acs (NOTINANY _) = List.all (not o is_RECEIVE) next_acs
        | action_order_check next_acs (NEW _) = List.all
            (fn a => is_NEW a orelse is_INSERT a orelse is_DELETE a orelse is_SEND a)
            next_acs
        | action_order_check next_acs (INSERT _) = List.all
            (fn a => is_NEW a orelse is_INSERT a orelse is_DELETE a orelse is_SEND a)
            next_acs
        | action_order_check next_acs (DELETE _) = List.all
            (fn a => is_NEW a orelse is_INSERT a orelse is_DELETE a orelse is_SEND a)
            next_acs
        | action_order_check next_acs (SEND _) = List.all is_SEND next_acs
        | action_order_check next_acs ATTACK = next_acs = []

      fun new_action_legal_type_annotations a =
        let
          fun f (TAtom a) = List.all (fn b => a <> b) new_action_illegal_annotations
            | f (TComp _) = false
        in
          case a of
            (NEW xs) => List.all (f o snd) xs
          | _ => true
        end

      val invalid_funs_in_msg =
        let
          val dist = distinct (op =)
          val conc = dist o List.concat o (fn (f,ms) => map f ms)
          fun f (Var _) = []
            | f (Const _) = []
            | f (Fun (g,ms)) =
                let val n = (g,length ms)
                    val ns = conc (f,ms)
                in if member (op =) fun_spec n then ns else dist (n::ns)
                end
            | f (Abbrev (_,ms)) = conc (f,ms)
            | f Attack = []
        in
          f
        end

      fun invalid_funs_in_action a =
        let
          val dist = distinct (op =)
          val conc = dist o List.concat o (fn (f,ms) => map f ms)
          val f = invalid_funs_in_msg
          fun fnc [] = []
            | fnc (INEQ (t,t')::ps) = t::t'::fnc ps
            | fnc (NOTIN (t,(_,ts))::ps) = t::ts@fnc ps
        in
          case a of
            (RECEIVE ts) => conc (f,ts)
          | (SEND ts) => conc (f,ts)
          | (EQUATION (t,t')) => conc (f,[t,t'])
          | (LETBINDING (t,t')) => conc (f,[t,t'])
          | (IN (t,(_,ts))) => conc (f,t::ts)
          | (NOTINANY (t,_)) => f t
          | (NEGCHECKS (_,ps)) => conc (f,fnc ps)
          | (INSERT (t,(_,ts))) => conc (f,t::ts)
          | (DELETE (t,(_,ts))) => conc (f,t::ts)
          | (NEW _) => []
          | ATTACK => []
        end

      fun invalid_sets_in_action a =
        let
          val dist = distinct (op =)
          val conc = dist o (fn (f,ns) => f ns)
          fun f [] = []
            | f ((s,SOME n)::ns) =
                if member (op =) set_spec (s,n) then f ns else (s,SOME n)::f ns
            | f ((s,NONE)::ns) =
                if member (op =) set_names s then f ns else (s,NONE)::f ns
          fun fnc [] = []
            | fnc (INEQ _::ps) = fnc ps
            | fnc (NOTIN (_,(s,ts))::ps) = (s,SOME (length ts))::fnc ps
        in
          case a of
            (RECEIVE _) => []
          | (SEND _) => []
          | (EQUATION _) => []
          | (LETBINDING _) => []
          | (IN (_,(s,ts))) => conc (f,[(s,SOME (length ts))])
          | (NOTINANY (_,s)) => conc (f,[(s,NONE)])
          | (NEGCHECKS (_,ps)) => conc (f,fnc ps)
          | (INSERT (_,(s,ts))) => conc (f,[(s,SOME (length ts))])
          | (DELETE (_,(s,ts))) => conc (f,[(s,SOME (length ts))])
          | (NEW _) => []
          | ATTACK => []
        end

      val invalid_funs_in_abbrevs =
        let
          val distconc = distinct (op =) o List.concat
          fun f (LABELED_ACTION (_,a)) = invalid_funs_in_action a
            | f (ABBREVIATION (_,ms)) = distconc (map invalid_funs_in_msg ms)
          fun g (TermAbbreviation ((s,_),m)) = (s,invalid_funs_in_msg m)
            | g (ActionsAbbreviation ((s,_),acs)) = (s,distconc (map f acs))
        in
          filter (fn (_,l) => l <> []) (map g (#abbreviation_spec trac))
        end

      val invalid_sets_in_abbrevs =
        let
          val distconc = distinct (op =) o List.concat
          fun f (LABELED_ACTION (_,a)) = invalid_sets_in_action a
            | f (ABBREVIATION _) = []
          fun g (TermAbbreviation ((s,_),_)) = (s,[])
            | g (ActionsAbbreviation ((s,_),acs)) = (s,distconc (map f acs))
        in
          filter (fn (_,l) => l <> []) (map g (#abbreviation_spec trac))
        end

      fun check_actions (tr_name,decl,acs) =
        let fun chk i =
              let val decl_flat = List.concat (map (fn (xs,t) => map (fn x => (x,t)) xs) decl)
                  val a = nth acs i
                  fun result st = (st,tr_name,a)
                  val fs = invalid_funs_in_action a
                  val gs = invalid_sets_in_action a
                  val prev_acs = List.take (acs,i)
                  val next_acs = List.drop (acs,i+1)
              in if fs <> []
                 then result (InvalidFunctionSymbols fs)
                 else if gs <> []
                 then result (InvalidSetSymbols gs)
                 else if not (set_action_param_check set_action_enum_params decl_flat a)
                 then result InvalidSetParam
                 else if not (action_order_check next_acs a)
                 then result WrongPosition
                 else if not (wfst decl_flat prev_acs next_acs a)
                 then result IllformedVars
                 else if not (new_action_legal_type_annotations a)
                 then result InvalidAnnotationNewAction
                 else result Passed
              end
        in map chk (0 upto (length acs - 1))
        end

      val checked_tr_acs = List.concat (map check_actions tr_acs)

      fun violating_action_exists' f =
        List.exists (f o #1) checked_tr_acs

      fun violating_action_exists status =
        violating_action_exists' (fn a => a = status)

      val violating_action_exists_unk_fun_sym =
        violating_action_exists' (fn a => case a of InvalidFunctionSymbols _ => true | _ => false)

      val violating_action_exists_unk_set_sym =
        violating_action_exists' (fn a => case a of InvalidSetSymbols _ => true | _ => false)

      fun violating_actions_str' f g =
        String.concatWith "\n" (
          map (fn (st,n,a) => g (st,n,action_str a))
              (filter (f o #1) checked_tr_acs))

      val violating_actions_str_unk_fun_sym =
        let
          fun f a = case a of InvalidFunctionSymbols fs => SOME fs | _ => NONE
        in
          violating_actions_str' (fn a => f a <> NONE)
            (fn (st,n,_) => "symbol(s) " ^
                            String.concatWith ", " (map (fn (s,n) => s ^ "/" ^ Int.toString n)
                                                        (Option.getOpt (f st, []))) ^
                            " in transaction \"" ^ n ^ "\"")
        end

      val violating_actions_str_unk_set_sym =
        let
          fun f a = case a of InvalidSetSymbols fs => SOME fs | _ => NONE
        in
          violating_actions_str' (fn a => f a <> NONE)
            (fn (st,n,_) => "symbol(s) " ^
                            String.concatWith ", "
                              (map (fn (s,n) => s ^ (case n of SOME n' => "/" ^ Int.toString n'
                                                             | _ => ""))
                                   (Option.getOpt (f st, []))) ^
                            " in transaction \"" ^ n ^ "\"")
        end

      fun violating_actions_str status =
        violating_actions_str'
          (fn a => a = status)
          (fn (_,n,a) => "action \"" ^ a ^ "\" in transaction \"" ^ n ^ "\"")
    in
      if has_dups tr_sec_names
      then error (
        "Multiple Transactions sections declared with the same name:\n" ^ dups_str tr_sec_names)
      else if has_dups tr_names
      then error (
        "Duplicate transaction declarations:\n" ^ dups_str tr_names)
      else if has_dups enumerations
      then error (
        "Multiple declarations of the same enumeration:\n" ^ dups_str enumerations)
      else if List.exists (fn n => n = value_trac_typeN) enumerations
      then error (
        "The special type \"" ^ value_trac_typeN ^ "\" should not be declared in the trac " ^
        "specification.")
      else if List.exists (fn n => n = enum_trac_typeN) enumerations
      then error (
        "The special type \"" ^ enum_trac_typeN ^ "\" should not be declared in the trac " ^
        "specification.")
      else if has_dups set_names
      then error (
        "Multiple declarations of the same set families:\n" ^ dups_str set_names)
      else if has_dups (fun_names@enum_consts)
      then error (
        "Multiple declarations of the same constant or function symbols:\n" ^
        dups_str (fun_names@enum_consts))
      else if has_dups ana_funs
      then error (
        "Multiple analysis rules declared for the same function symbols:\n" ^ dups_str ana_funs)
      else if has_dups abb_funs
      then error (
        "Multiple abbreviations declared with the same name:\n" ^ dups_str abb_funs)
      else if List.exists has_dups ana_args
      then error (
        "The heads of the analysis rules must be linear terms, " ^
        "i.e., of the form f(X1,...,Xn) for distinct X1,...,Xn.\n" ^
        "The analysis rules with the following heads violate this condition:\n" ^
        String.concatWith "\n" (
          map (fn i => nth ana_funs i ^ "(" ^ String.concatWith "," (nth ana_args i) ^ ")")
              (filter (has_dups o (nth ana_args)) (0 upto (length (#analysis_spec trac) - 1)))))
      else if List.exists ana_has_illegal_var_in_body (#analysis_spec trac)
      then error (
        "Variables occurring in the body of an analysis rule must also occur in its head.\n" ^
        "The analysis rules with the following heads violate this condition:\n" ^
        String.concatWith "\n" (
          map (fn i => nth ana_funs i ^ "(" ^ String.concatWith "," (nth ana_args i) ^ ")")
              (filter (ana_has_illegal_var_in_body o (nth (#analysis_spec trac)))
                      (0 upto (length (#analysis_spec trac) - 1)))))
      else if List.exists has_dups abb_args
      then error (
        "The heads of the abbreviation declarations must be linear terms, " ^
        "i.e., of the form f[X1,...,Xn] for distinct X1,...,Xn.\n" ^
        "The abbreviation declaration with the following heads violate this condition:\n" ^
        String.concatWith "\n" (
          map (fn i => nth abb_funs i ^ "![" ^ String.concatWith "," (nth abb_args i) ^ "]")
              (filter (has_dups o (nth abb_args)) (0 upto (length (#abbreviation_spec trac) - 1)))))
      else if List.exists abb_has_illegal_var_in_body (#abbreviation_spec trac)
      then error (
        "Variables occurring in the body of an abbreviation declaration must also occur in its " ^
        "head.\nThe abbreviation declarations with the following heads violate this condition:\n" ^
        String.concatWith "\n" (
          map (fn i => nth abb_funs i ^ "![" ^ String.concatWith "," (nth abb_args i) ^ "]")
              (filter (abb_has_illegal_var_in_body o (nth (#abbreviation_spec trac)))
                      (0 upto (length (#abbreviation_spec trac) - 1)))))
      else if not (null user_types_overlapping_enums)
      then error (
        "Types declared in the \"Types\" section cannot also be declared as enumerations in " ^
        "the \"Enumerations\" section.\nThe following types violate this condition:\n" ^
        String.concatWith ", " user_types_overlapping_enums)
      else if List.exists (List.exists var_decl_has_illegal_type o snd) tr_hds
      then error (
        "Transactions must satisfy certain well-formedness requirements on the variables " ^
        "declared in their heads:\n" ^
        "1. The only special atomic types that may occur in the variable declarations are " ^
        "\"" ^ value_trac_typeN ^ "\" and \"" ^ enum_trac_typeN ^ "\". In particular, the " ^
        "following special types are not allowed: " ^
        String.concatWith ", " illegal_atomic_types ^ "\n" ^
        "2. For variables declared with composed types no enumeration or special type besides " ^
        "\"" ^ enum_trac_typeN ^ "\" may occur in their types. In particular, the following " ^
        "cannot occur in composed types: " ^
        String.concatWith ", " illegal_composed_type_subterms ^ "\n" ^
        "3. The number of parameters applied to a composed type must agree with the arity of " ^
        "the function symbol associated with that type.\n" ^
        "The following variable declarations violate these requirements:\n" ^
        String.concatWith "\n" (
          map_filter (fn (n,decls) =>
                            let val ds =
                                  List.concat (map (fn (xs,t) => map (fn x => (x,t)) xs) decls)
                                val ds' = filter var_decl_has_illegal_type ds
                            in if null ds' then NONE
                            else SOME (String.concatWith "\n"
                                        (map (fn (s,t) => s ^ ": " ^ MsgType_str t) ds') ^
                                       " in transaction " ^ n)
                            end)
                     tr_hds))
      else if invalid_funs_in_abbrevs <> []
      then error (
        "Function symbols occurring in abbreviations in the \"Abbreviations\" section must be " ^
        "declared in the \"Functions\" section and must be applied with the correct number of " ^
        "arguments.\nThe following function symbols violate this requirement:\n" ^
        String.concatWith "\n" (
          map (fn (ab,fs) =>
                "symbol(s) " ^
                String.concatWith ", " (map (fn (f,n) => f ^ "/" ^ Int.toString n) fs) ^
                " in abbreviation \"" ^ ab ^ "\"")
              invalid_funs_in_abbrevs))
      else if invalid_sets_in_abbrevs <> []
      then error (
        "Set symbols occurring in abbreviations in the \"Abbreviations\" section must be " ^
        "declared in the \"Sets\" section and must be applied with the correct number of " ^
        "arguments.\nThe following set symbols violate this requirement:\n" ^
        String.concatWith "\n" (
          map (fn (ab,fs) =>
                "symbol(s) " ^
                String.concatWith ", " (
                  map (fn (f,n) => f ^ (case n of SOME n' => "/" ^ Int.toString n' | _ => ""))
                      fs) ^
                " in abbreviation \"" ^ ab ^ "\"")
              invalid_sets_in_abbrevs))
      else if violating_action_exists_unk_fun_sym
      then error (
        "Function symbols occurring in transactions in the \"Transactions\" section must be " ^
        "declared in the \"Functions\" section and must be applied with the correct number of " ^
        "arguments.\nThe following function symbols violate this requirement:\n" ^
        violating_actions_str_unk_fun_sym)
      else if violating_action_exists_unk_set_sym
      then error (
        "Set symbols occurring in transactions in the \"Transactions\" section must be " ^
        "declared in the \"Sets\" section and must be applied with the correct number of " ^
        "arguments.\nThe following set symbols violate this requirement:\n" ^
        violating_actions_str_unk_set_sym)
      else if violating_action_exists WrongPosition
      then error (
        "The sequence of actions occurring in each transaction must either be of the form " ^ 
        "(written here in standard regular expression syntax)\n" ^
        "  (receive t)* (x in s | x notin s | let t = t' | t == t' | t != t')* " ^
        "(new x | insert x s | delete x s)* (send t)*\n" ^
        "or of the form\n" ^
        "  (receive t)* (x in s | x notin s | let t = t' | t == t' | t != t')* attack\n" ^
        "The following actions lead to violations of these requirements:\n" ^
        violating_actions_str WrongPosition)
      else if violating_action_exists IllformedVars
      then error (
        "The following well-formedness requirement on the occurrences of variables in " ^
        "transactions must be satisfied:\n" ^ 
        "1. Variables in \"send\", \"in\", \"notin\", \"let\", \"==\", and \"!=\" actions must " ^
        "be declared in the head of the transaction where these actions occur, or, in the case " ^
        "of negative checks, be bound by a \"forall\" quantifier.\n" ^
        "2. Variables in a \"new\" action must not occur previously in the same transaction, " ^
        "they must be distinct, and they must each occur in either an \"insert\" or a \"send\" " ^
        "action in the same transaction.\n" ^
        "3. Variables in \"insert\", \"delete\", and \"send\" actions must occur previously " ^
        "in the same transaction.\n" ^
        "The following actions lead to violations of these requirements:\n" ^
        violating_actions_str IllformedVars)
      else if violating_action_exists InvalidAnnotationNewAction
      then error (
        "Annotating variables in \"new\" actions with either enumerations, composed types, or " ^
        "special types besides \"" ^ value_trac_typeN ^ "\" is not allowed.\nIn particular, the " ^
        "following enumerations and atomic types cannot be used in \"new\" actions:\n" ^
        String.concatWith ", " new_action_illegal_annotations ^ "\n" ^
        "The following actions violate this requirement:\n" ^
        violating_actions_str InvalidAnnotationNewAction)
      else let
        val ws = [
          (violating_action_exists InvalidSetParam,
           "The parameters to a set-expression must be finite enumerations declared in the " ^
           "\"Enumerations\" section of the trac specification, and must furthermore be " ^
           "declared in the transaction where the set-expression occurs. In particular, they " ^
           "must not be variables of type \"" ^ value_trac_typeN ^ "\".\n" ^
           "The following actions violate these requirements:\n" ^
           violating_actions_str InvalidSetParam)
           ]
        val _ = if List.exists fst ws
                then let
                  val _ = warning ("Warning: The specification is not suitable for automated " ^
                                   "verification. To enable automation the following issues " ^
                                   "need to be resolved:")
                in fold (fn (b,w) => fn _ => if b then warning w else ()) ws () end
                else ()
      in trac end
    end

fun certifyProtocol (trac:protocol) =
  let
    fun expand_abbreviations (trac:protocol) =
      let
        val expand_tabbs  = expand_term_abbreviations (get_term_abbreviations_trac trac)
        val expand_taabbs = expand_term_abbreviations_in_action (get_term_abbreviations_trac trac)
        val expand_aabbs  = map (fn (lbl,ac) => LABELED_ACTION (lbl,expand_taabbs ac)) o
                            expand_action_abbreviations (get_action_abbreviations_trac trac)
      in
        ({name = #name trac
         ,type_spec = #type_spec trac
         ,enum_spec = #enum_spec trac
         ,set_spec = #set_spec trac
         ,function_spec = #function_spec trac
         ,analysis_spec =
            map (fn (h,ks,rs) => (h,map expand_tabbs ks,rs)) (#analysis_spec trac)
         ,abbreviation_spec = []
         ,transaction_spec =
            map (fn (n,trs) =>
                  (n,map (fn tr => {transaction=(#transaction tr),
                                    actions=(expand_aabbs (#actions tr))})
                         trs))
                (#transaction_spec trac)
         ,fixed_point =
            Option.map (map (fn (t,xs) => (expand_tabbs t,xs))) (#fixed_point trac)
        })
      end

    fun transform_cAction (trac:protocol) =
      let
        val pfe = transform_cMsg trac
        val pte = priv_fun_type_enc trac
        fun pne (cInequality (t,t')) = cInequality (pfe t,pfe t')
          | pne (cNotInSet (t,t')) = cNotInSet (pfe t,pfe t')
        fun aux (cReceive ts) = cReceive (map pfe ts)
          | aux (cSend ts) = cSend (map pfe ts)
          | aux (cEquality (psv,(t,t'))) = cEquality (psv,(pfe t,pfe t'))
          | aux (cInSet (psv,(t,t'))) = cInSet (psv,(pfe t,pfe t'))
          | aux (cNotInAny (t,s)) = cNotInAny (pfe t,s)
          | aux (cNegChecks (xs,ns)) = cNegChecks (map (fn (x,tau) => (x,pte tau)) xs, map pne ns)
          | aux (cInsert (t,t')) = cInsert (pfe t,pfe t')
          | aux (cDelete (t,t')) = cDelete (pfe t,pfe t')
          | aux (cNew xs) = cNew (map (fn (x,tau) => (x,pte tau)) xs)
          | aux cAssertAttack = cAssertAttack
      in aux end

    fun transform_cTransaction (trac:protocol) (tr:cTransaction) =
      let
        val pae = map (fn (lbl,ac) => (lbl,transform_cAction trac ac))
        val pte = priv_fun_type_enc trac
      in
       {transaction=(case (#transaction tr) of (a,b,c) => (a,map (fn (x,tau) => (x,pte tau)) b,c))
       ,receive_actions=pae (#receive_actions tr)
       ,checksingle_actions=pae (#checksingle_actions tr)
       ,checkall_actions=pae (#checkall_actions tr)
       ,fresh_actions=pae (#fresh_actions tr)
       ,update_actions=pae (#update_actions tr)
       ,send_actions=pae (#send_actions tr)
       ,attack_actions=pae (#attack_actions tr)}
      end

    fun certify (trac:protocol) =
      let
        val certify_ana_msg = transform_cMsg trac o certifyMsgUntyped
        val certify_type = priv_fun_type_enc trac o
                           certifyMsgType' (get_finite_enum_names_trac trac)
                                           (get_infinite_enum_names_trac trac)
        val certify_transaction = transform_cTransaction trac o
                                  certifyTransaction (get_finite_enum_names_trac trac)
                                                     (get_infinite_enum_names_trac trac)

        val cert_fun_spec =
          let
            fun invalid (_,n,SOME (Trac_Term.TAtom _)) = n <> 0
              | invalid (_,_,SOME (Trac_Term.TComp _)) = true
              | invalid (_,_,NONE) = false
            val _ = case #function_spec trac of
                      SOME {private=priv, public=pub} =>
                        if List.exists invalid (priv@pub)
                        then error ("Error: Invalid type annotation in function specification. " ^
                                    "Only constants may be annotated with types, and only with " ^
                                    "atomic types.")
                        else ()
                    | NONE => ()

            fun cert_const (a,b,c) =
              if b = 0
              then (a,Option.map (fn tau =>
                        (case certify_type tau of
                            AtomicType s => s
                          | _ => error ("Error: Invalid type annotation in function " ^
                                        "specification: " ^ MsgType_str tau))) c)
              else error ("Error: Expected arity 0 for function symbol " ^ a ^
                          " but got " ^ Int.toString b)
            fun cert_fun (a,b,c) =
              case c of
                NONE => (a,b)
              | SOME tau =>
                  error ("Error: Expected no type annotation for function symbol " ^ a ^
                         " but got " ^ MsgType_str tau)
          in
            if #function_spec trac = NONE then NONE
            else case get_funs_trac trac of
              (pub_funs, pub_consts, priv_consts) =>
                SOME ({private_consts=map cert_const priv_consts,
                       public_consts=map cert_const pub_consts,
                       public_funs=map cert_fun pub_funs})
          end

        val cert_ana_spec =
          let
            val (pub_f, _, _) = get_funs_trac trac
            fun ana_arity (f,n) = (if is_priv_fun_trac trac f then n-1 else n)
            fun check_valid_arity ((f,ps),ks,rs) =
              case List.find (fn g => f = #1 g) pub_f of
                SOME (f',n,_) =>
                  if length ps <> ana_arity (f',n)
                  then error ("Error: Invalid number of parameters in the analysis rule for " ^ f ^
                              " (expected " ^ Int.toString (ana_arity (f',n)) ^
                              " but got " ^ Int.toString (length ps) ^ ")")
                  else ((f,ps),ks,rs)
              | NONE => error ("Error: " ^ f ^
                                " is not a declared function symbol of arity greater than zero")
          in
            map (fn (h,ks,rs) => {
                  head=h, keys=map certify_ana_msg ks,
                  results=rs, is_priv_fun=is_priv_fun_trac trac (fst h)})
                (map check_valid_arity (#analysis_spec trac))
          end

        val (cert_transaction_spec:(string option * cTransaction list) list) =
          map (fn (n,trs) => (n,map certify_transaction trs))
              (#transaction_spec trac)

        val cert_fp =
          Option.map (certify_fixpoint trac) (#fixed_point trac)
      in
        ({name = #name trac
         ,type_spec = #type_spec trac
         ,enum_spec = flatten_enum_spec_trac trac
         ,set_spec = #set_spec trac
         ,function_spec = cert_fun_spec
         ,analysis_spec = cert_ana_spec
         ,transaction_spec = cert_transaction_spec
         ,fixed_point = cert_fp
        })
      end

    fun add_intruder_value_gen_transaction (trac:protocol) =
      let
        val spec_tr_names =
          List.concat (map (map (#1 o #transaction) o snd) (#transaction_spec trac))
        val spec_set_names = map #1 (#set_spec trac)
        val spec_protnames =
          let
            val optnames = map #1 (#transaction_spec trac)
            val names = map_index (fn (n,optn) => Option.getOpt (optn,Int.toString n)) optnames
          in names end
        val spec_atmost1prot = case spec_protnames of (_::_::_) => false | _ => true

        fun name_free ns n = List.all (fn s => s <> n) ns
        fun gen_name prefix names n =
          if name_free names prefix then prefix
          else if name_free names (prefix ^ Int.toString n) then prefix ^ Int.toString n
          else gen_name prefix names (n+1)

        val set_def = (gen_name "intruderValues" spec_set_names 0,0,false):set_spec_elem

        fun tr_name suffix =
          let val s = if spec_atmost1prot then "" else "_" ^ suffix
          in (gen_name ("intruderValueGen" ^ s) spec_tr_names 0,[],[]):transaction_name end

        fun valuegentr protname = {
          transaction=tr_name protname,
          actions=[
            LABELED_ACTION (LabelS,NEW [(["X"],TAtom(value_trac_typeN))]),
            LABELED_ACTION (LabelS,INSERT (Var "X",(#1 set_def,[]))),
            LABELED_ACTION (LabelS,SEND [Var "X"])
          ]}:transaction

        val expand_abbrevs =
          expand_action_abbreviations (get_action_abbreviations_trac trac)

        val checks_and_deletes_sets =
          let
            fun f a = case a of
              DELETE (_,(s,_)) => [s]
            | IN (_,(s,_)) => [s]
            | NOTINANY (_,s) => [s]
            | NEGCHECKS (_,bs) =>
                map_filter (fn b => case b of NOTIN (_,(s,_)) => SOME s | _ => NONE) bs
            | _ => []

            val acs = List.concat (map #actions (List.concat (map (#2) (#transaction_spec trac))))
            val sets = List.concat (map (f o #2) (expand_abbrevs acs))
          in sets end

        fun has_valuegentr (trs:transaction list) =
          let fun is_valuegentr_variant1 acs = case acs of
                [LABELED_ACTION (LabelS,NEW [([x],TAtom(tau))]),
                 LABELED_ACTION (lbl,SEND ts)]
                  => tau = value_trac_typeN andalso
                     member (op =) ts (Var x) andalso
                     (lbl = LabelS orelse spec_atmost1prot)
              | _ => false

              fun is_valuegentr_variant2 acs = case acs of
                [LABELED_ACTION (LabelS,NEW [([x],TAtom(tau))]),
                 LABELED_ACTION (lbl,INSERT (y,(s,[]))),
                 LABELED_ACTION (lbl',SEND ts)]
                  => tau = value_trac_typeN andalso
                     member (op =) ts (Var x) andalso
                     y = Var x andalso
                     not (member (op =) checks_and_deletes_sets s) andalso
                     ((lbl = LabelS andalso lbl' = LabelS) orelse spec_atmost1prot)
              | _ => false

              fun is_valuegentr {transaction=(_,args,ineqs),actions=acs} =
                List.null args andalso List.null ineqs andalso
                (is_valuegentr_variant1 acs orelse is_valuegentr_variant2 acs)
          in List.exists (is_valuegentr) trs end
      in
        ({name = #name trac
        ,type_spec = #type_spec trac
        ,enum_spec = #enum_spec trac
        ,set_spec = set_def::(#set_spec trac)
        ,function_spec = #function_spec trac
        ,analysis_spec = #analysis_spec trac
        ,abbreviation_spec = #abbreviation_spec trac
        ,transaction_spec =
            map_index (fn (i,(n,trs)) =>
                            if has_valuegentr trs then (n,trs)
                            else (n,valuegentr (nth spec_protnames i)::trs))
                      (#transaction_spec trac)
        ,fixed_point = #fixed_point trac
        }):protocol
      end
  in
    (trac |> check_for_invalid_trac_specification
          |> add_intruder_value_gen_transaction
          |> expand_abbreviations
          |> certify
    ):cProtocol
  end


end
\<close>


end
