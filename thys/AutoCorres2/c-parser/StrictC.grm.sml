functor StrictCLrValsFun(structure Token : TOKEN)
 : sig structure ParserData : PARSER_DATA
       structure Tokens : StrictC_TOKENS
   end
 = 
struct
structure ParserData=
struct
structure Header = 
struct
(**
 ** Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 ** Copyright (c) 2022 Apple Inc. All rights reserved.
 **
 ** SPDX-License-Identifier: BSD-2-Clause
 **)

open Absyn NameGeneration
val errorStr' = Feedback.errorStr'
val warnStr' = Feedback.warnStr'
val bogus = SourcePos.bogus

fun lleft [] = bogus
  | lleft (h :: t) = left h
fun lright [] = bogus
  | lright x = right (List.last x)
type adecl = (expr ctype -> expr ctype) wrap
type 'a ddecl = string wrap
                * adecl
                * (expr ctype * string wrap option) wrap list option
                * 'a list
type addecl = gcc_attribute ddecl

(* composition of declarators *)
fun ooa(adec1, adec2) = let
  (* composition of abstract declarators *)
  val a1 = node adec1
  val a2 = node adec2
in
  wrap(a1 o a2, left adec1, right adec2)
end

fun ood(ddw, adec) = let
  val (nm, adec0, params, data) = node ddw
in
  wrap((nm, ooa(adec0,adec), params, data), left ddw, right adec)
end

infix ood

fun add_attributes(ddw, attrs) = let
  val (nm, adec, ps, data0) = node ddw
in
  wrap((nm, adec, ps, attrs @ data0), left ddw, right ddw)
end


fun addparams(dw : 'a ddecl wrap, ps) : 'a ddecl wrap = let
  val (nm, a, pso, data) = node dw
in
  case pso of
    SOME _ => dw
  | NONE => wrap((nm,a,SOME ps,data), left dw, right dw)
end

fun check_params ctxt
      (plist : (expr ctype * string wrap option) wrap list wrap)
      : (expr ctype * string wrap option) wrap list =
    case node plist of
      [] => (Feedback.warnStr' ctxt (left plist, right plist,
                               "Avoid empty parameter lists in C; \
                               \prefer \"(void)\"");
             [])
    | x as [tysw] => (case node tysw of
                        (Void, NONE) => []
                      | _ => x)
    | x => x



fun fndecl l r (ps : expr ctype list) =
    wrap((fn ty => Function(ty, ps)), l, r)
fun ptrdecl l r = wrap (Ptr, l, r)
fun arraydecl l r n = wrap ((fn ty => Array (ty, n)), l, r)

val one_const = expr_int 1
val zero_const = expr_int 0
fun postinc e = Assign(e,ebogwrap(BinOp(Plus,e,one_const)))
fun postdec e = Assign(e,ebogwrap(BinOp(Minus,e,one_const)))


fun resolve_fnname ctxt e =
    case enode e of
      Var (s,_) => s
    | _ => (errorStr' ctxt (eleft e, eright e,
                      "Can't use this expression as function name");
            "_bad name_")


fun handle_builtin_fns ctxt e =
    case enode e of
      EFnCall (fn_e, args) => let
      in
        case enode fn_e of
          Var(s,_) =>
          if s = NameGeneration.mkIdentUScoreSafe "__builtin_expect" then
            case args of
              [x,y] => x
            | _ => (Feedback.errorStr' ctxt (eleft e, eright e,
                                       "__builtin_expect must take 2 args.");
                    expr_int 0)
          else e
        | _ => e
      end
    | _ => e

fun delvoidcasts e =
    case enode e of
      TypeCast (tywrap, e0) => let
      in
        case node tywrap of
          Void => e0
        | _ => e
      end
    | _ => e


fun parse_stdassignop ctxt (e1,opn,e2) = let
  val e2 = handle_builtin_fns ctxt e2
  val r_e = case opn of
              NONE => e2
            | SOME abop => ewrap(BinOp(abop,e1,e2), eleft e2, eright e2)
in
  case enode e2 of
    EFnCall (f_e, args) => let
      fun e_ok e =
          case enode e of
            Var _ => true
          | StructDot(e0, fld) => e_ok e0
          | _ => false
    in
      if e_ok e1 andalso opn = NONE then
        AssignFnCall(SOME e1, f_e, args)
      else
        Assign(e1,r_e)
    end
  | _ => Assign(e1,r_e)
end

fun check_names ctxt (fname:string) plist = let
  fun check i ps =
      case ps of
        [] => []
      | pw :: rest =>
          (case node pw of
             (ty, SOME nm) => (ty,nm) :: check (i + 1) rest
           | (ty, NONE) => (errorStr' ctxt (left pw, right pw,
                                      "Parameter #"^Int.toString i^
                                      " of function "^fname^
                                      " has no name");
                            (ty, wrap("__fake", bogus, bogus)) ::
                            check (i + 1) rest))
in
  check 1 plist
end

type struct_field = (expr ctype * string wrap * expr option * gcc_attribute list)
type struct_fields = struct_field list
type struct_id_decl = string wrap * struct_fields * gcc_attribute list wrap

fun extract_unions_and_structs (sd: struct_id_decl) =
  sd |> #2 |> map #1 |> map CType.nested_types |> flat
  |> filter (fn ty => CType.is_struct_type ty orelse CType.is_union_type ty)

local val scount = Unsynchronized.ref 0
in
fun gen_struct_id () =
      (scount := !scount + 1;
       NameGeneration.internalAnonStructPfx^Int.toString (!scount))
end

datatype storage_class_specifier = TypeDef | Extern | Static | Auto | Register | Thread_Local
datatype type_qualifier = Const | Volatile | Restrict
datatype typespectok = ts_unsigned
                     | ts_signed
                     | ts_bool
                     | ts_char
                     | ts_int
                     | ts_long
                     | ts_longlong
                     | ts_int128
                     | ts_short
                     | ts_void
type struct_or_union_specifier = expr ctype wrap * struct_id_decl wrap list
type enum_specifier = (string option wrap *
                       (string wrap * expr option) list) wrap
datatype type_specifier = Tstok of typespectok wrap
                        | Tsstruct of struct_or_union_specifier
                        | Tsenum of enum_specifier
                        | Tstypeid of string wrap
                        | Tstypeof of expr wrap
fun tsleft (Tstok tok) = left tok
  | tsleft (Tsstruct (ty, _)) = left ty
  | tsleft (Tstypeid s) = left s
  | tsleft (Tsenum es) = left es
  | tsleft (Tstypeof e) = left e
fun tsright (Tstok tok) = right tok
  | tsright (Tsstruct (ty,_)) = right ty
  | tsright (Tstypeid s) = right s
  | tsright (Tsenum es) = right es
  | tsright (Tstypeof e) = right e

datatype decl_specifier = Storage of storage_class_specifier wrap
                        | TypeQual of type_qualifier wrap
                        | TypeSpec of type_specifier
                        | FunSpec of Absyn.fnspec wrap

fun scs_to_SC scs =
  case scs of
      Extern => SOME SC_EXTERN
    | Static => SOME SC_STATIC
    | Thread_Local => SOME SC_THRD_LOCAL
    | Register => SOME SC_REGISTER
    | Auto => SOME SC_AUTO
    | TypeDef => NONE

val extract_storage_specs =
  List.mapPartial (fn Storage scs_w => scs_to_SC (node scs_w)
                    | _ => NONE)

fun dslleft [] = raise Fail "dslleft: nil"
  | dslleft (h :: t) =
    case h of
      Storage s => left s
    | TypeQual s => left s
    | FunSpec s => left s
    | TypeSpec ts => tsleft ts
fun dslright dsl =
    case dsl of
      [] => raise Fail "dslright: nil"
    | [h] => (case h of
                Storage s => right s
              | TypeQual s => right s
              | FunSpec s => right s
              | TypeSpec ts => tsright ts)
    | h::t => dslright t


fun parse_siddecl ctxt (kind: expr ctype, s : struct_id_decl wrap) : declaration wrap =
  let
    val (nm, fields, attrs) = node s
    val decl = case kind of StructTy _ => StructDecl | UnionTy _ => UnionDecl
             | _ => (errorStr' ctxt (left s, right s, "Expected 'struct' or 'union'"); StructDecl)
    fun f (ty : expr ctype, s : string wrap, opbit : expr option, attrs : gcc_attribute list) =
      let
        val ty' : expr ctype =
            case opbit of
              NONE => ty
            | SOME e =>  Bitfield(ty, e)
      in
        (ty',s,attrs)
      end
    val fields' = map f fields
  in
    wrap(decl(nm, fields', attrs), left s, right s)
  end

fun tag_siddecls ty sdecls =
  let
    val unions_and_structs = sdecls |> map node |> map extract_unions_and_structs |> flat

    fun match name (CType.UnionTy s) = (s = name)
      | match name (CType.StructTy s) = (s = name)
      | match _ _ = false

    fun tag tys sd =
      let
        val name = sd |> node |> #1 |> node
        val ty = the (find_first (match name) tys)
      in
        (ty, sd)
      end
  in
    map (tag (node ty::unions_and_structs)) sdecls
  end


fun empty_enumspec es = [(wrap(EnumDecl (node es), left es, right es))]
fun empty_declarator ctxt (ds : decl_specifier list) : declaration wrap list =
    case ds of
      [] => raise Fail "empty_declarator: nil"
    | Storage x :: rest =>
                (errorStr' ctxt (left x, right x,
                           "Storage class qualifier not accompanied by \
                           \declarator");
                 empty_declarator ctxt rest)
    | TypeQual tq :: rest =>
                 (errorStr' ctxt (left tq, right tq,
                            "Type-qualifier not accompanied by declarator");
                  empty_declarator ctxt rest)
    | FunSpec fs :: rest =>
                 (errorStr' ctxt (left fs, right fs,
                            "Function-specifier not accompanied by declarator");
                  empty_declarator ctxt rest)
    | TypeSpec (Tstok tok) :: rest =>
                 (errorStr' ctxt (left tok, right tok,
                            "Type not accompanied by declarator");
                  empty_declarator ctxt rest)
    | TypeSpec (Tstypeid s) :: rest =>
                 (errorStr' ctxt (left s, right s,
                            "Type-id ("^node s^ ") not accompanied by declarator");
                  empty_declarator ctxt rest)
    | [TypeSpec (Tsstruct (kind, siddecls))] =>
        (map (parse_siddecl ctxt)) (tag_siddecls kind siddecls)
    | TypeSpec (Tsstruct s) :: rest =>
                 (errorStr' ctxt (dslleft rest, dslright rest,
                            "Extraneous crap after struct declaration");
                  empty_declarator ctxt [TypeSpec (Tsstruct s)])
    | [TypeSpec (Tsenum es)] => empty_enumspec es
    | TypeSpec (Tsenum es) :: rest =>
                 (errorStr' ctxt (dslleft rest, dslright rest,
                            "Extraneous crap after enum declaration");
                  empty_enumspec es)

fun ity_of_tok tstok =
    case node tstok of
      ts_int => Int
    | ts_char => Char
    | ts_short => Short
    | ts_long => Long
    | ts_longlong => LongLong
    | ts_int128 => Int128
    | x => raise Fail "ty_of_tok: invariant failure"

fun sort_toks (bases, sgnmods) dsl =
    case dsl of
      [] => (bases, sgnmods)
    | TypeSpec (Tstok tk) :: r =>
            (case node tk of
               ts_unsigned => sort_toks (bases, tk :: sgnmods) r
             | ts_signed => sort_toks (bases, tk :: sgnmods) r
             | _ => sort_toks (wrap(Tstok tk, left tk, right tk) :: bases,
                               sgnmods) r)
    | TypeSpec (x as Tsstruct (ty,_)) :: r =>
        sort_toks (wrap(x, left ty, right ty)::bases, sgnmods) r
    | TypeSpec (x as Tstypeid sw) :: r =>
        sort_toks (wrap(x,left sw,right sw)::bases, sgnmods) r
    | TypeSpec (x as Tsenum es) :: r =>
        sort_toks (wrap(x,left es, right es)::bases, sgnmods) r
    | TypeSpec (x as Tstypeof e) :: r =>
        sort_toks (wrap(x,left e, right e)::bases, sgnmods) r
    | _ :: r => sort_toks (bases, sgnmods) r

fun extract_fnspecs (dsl : decl_specifier list) : fnspec list =
    List.mapPartial (fn FunSpec fs => SOME (node fs) | _ => NONE) dsl

fun extract_fnspec_attrs (fs : fnspec list) : gcc_attribute list =
  case fs of
      [] => []
    | gcc_attribs gcc_as::rest => gcc_as @ extract_fnspec_attrs rest
    | _ :: rest => extract_fnspec_attrs rest

fun extract_type ctxt (dsl : decl_specifier list wrap) : expr ctype wrap = let
  val (bases : type_specifier wrap list,
       sgnmods : typespectok wrap list) = sort_toks ([], []) (node dsl)
  fun is_base b (tn : type_specifier wrap) =
      case node tn of
          Tstok t => node t = b
        | _ => false
  fun is_intmod (tn : type_specifier wrap) =
      case node tn of
          Tstok t => (case node t of
                          ts_short => true
                        | ts_long => true
                        | _ => false)
        | _ => false
  fun handle_integral_remainder had_int list =
      case list of
          [] => NONE
        | [x] => if had_int then
                   if is_intmod x then SOME x
                   else
                     (errorStr' ctxt (left x, right x, "Bad combination with 'int'");
                      SOME x)
                 else SOME x
        | [x,y] => (case (node x, node y) of
                        (Tstok k1, Tstok k2) => let
                          (* order here is reverse of occurrence in input *)
                          val l = left y and r = right x
                        in
                          if node k1 = ts_long andalso node k2 = ts_long then
                            SOME (wrap (Tstok (wrap(ts_longlong, l, r)), l, r))
                          else
                            (errorStr' ctxt (l, r, "Two type-specifiers"); SOME x)
                        end
                      | _ => (errorStr' ctxt (left x, right x, "Two type-specifiers");
                              SOME x))
        | h::t => (errorStr' ctxt (left h, right h, "Too many type-specifiers");
                   SOME h)

  fun check_baseclashes list =
      case list of
        [] => NONE
      | [x] => SOME x
      | _ =>
        case List.partition (is_base ts_int) list of
            ([], _) => handle_integral_remainder false list
          | ([_], rest) => handle_integral_remainder true rest
          | (t::_, _) => (errorStr' ctxt (left t, right t, "Too many 'int' specifiers");
                          SOME t)

  fun check_modclashes list =
      case list of
        [] => NONE
      | [x] => SOME x
      | h :: t => (errorStr' ctxt (left h, right h, "Multiple type-specifiers");
                   SOME h)
  val basety = check_baseclashes bases
  val sgnmod = check_modclashes sgnmods
in
  case (basety, sgnmod) of
    (NONE, NONE) => (errorStr' ctxt (left dsl, right dsl,
                               "No base type in declaration");
                     wrap(Signed Int, bogus, bogus))
  | (SOME b, NONE) => let
    in
      case node b of
        Tstok tk => (case node tk of
                       ts_void => wrap(Void, left tk, right tk)
                     | ts_char => wrap(PlainChar, left tk, right tk)
                     | ts_bool => wrap(Bool, left tk, right tk)
                     | x => wrap(Signed (ity_of_tok tk),
                                 left tk, right tk))
      | Tsstruct (ty, _) => ty
      | Tstypeid s => wrap(Ident (node s), left s, right s)
      | Tsenum e => wrap (EnumTy (node (#1 (node e))), left e, right e)
      | Tstypeof e => wrap (TypeOf (node e), left e, right e)
    end
  | (NONE, SOME m) =>
    (case node m of
       ts_unsigned => wrap(Unsigned Int, left m, right m)
     | ts_signed => wrap (Signed Int, left m, right m)
     | x => raise Fail "finalty2: inv failure")
  | (SOME b, SOME m) =>
     case node b of
       Tstok tk =>
       (case node tk of
            ts_void => (errorStr' ctxt (left m, right m,
                                  "Signedness modifier on void");
                        wrap(Void, left tk, right tk))
          | ts_bool => (errorStr' ctxt (left m, right m,
                                  "Signedness modifier on _Bool");
                        wrap(Bool, left tk, right tk))
          | _ =>
            let
            in
              case node m of
                  ts_unsigned => wrap(Unsigned (ity_of_tok tk),
                                      left m, right tk)
                | ts_signed => wrap(Signed (ity_of_tok tk),
                                    left m, right tk)
                | x => raise Fail "finalty3: inv failure"
            end)
     | Tstypeid s => (errorStr' ctxt (left m, right m,
                                "Signedness modifier on typedef id");
                      wrap(Ident (node s), left s, right s))
     | Tsstruct (ty,_) => (errorStr' ctxt (left m, right m,
                                    "Signedness modifier on struct");
                          ty)
     | Tsenum e => (errorStr' ctxt (left m, right m, "Signedness modifier on enum");
                    wrap(EnumTy (node (#1 (node e))), left e, right e))
     | Tstypeof e => (errorStr' ctxt (left m, right m, "Signedness modifier on typeof");
                    wrap(TypeOf (node e), left e, right e))
end

(* returns a (SourcePos.t * SourcePos.t) option *)
fun has_typedef (dsl : decl_specifier list wrap) = let
  fun check dsls =
      case dsls of
        [] => NONE
      | Storage s :: rest =>
                (case node s of TypeDef => SOME (left s, right s)
                              | _ => check rest)
      | _ :: rest => check rest
in
  check (node dsl)
end

(* returns a (SourcePos.t * SourcePos.t) option *)
fun has_extern (dsl : decl_specifier list wrap) = let
  fun check dsls =
      case dsls of
        [] => NONE
      | Storage s :: rest => (case node s of Extern => SOME (left s, right s)
                                           | _ => check rest)
      | _ :: rest => check rest
in
  check (node dsl)
end


fun first_sdecls (dsl : decl_specifier list) =
    case dsl of
      [] => []
    | TypeSpec (Tsstruct(ty, sdecls)) :: _ => sdecls
    | _ :: rest => first_sdecls rest



fun tag_first_sdecls (dsl : decl_specifier list) =
    case dsl of
      [] => []
    | TypeSpec (Tsstruct(ty, sdecls)) :: _ => tag_siddecls ty sdecls
    | _ :: rest => tag_first_sdecls rest

fun first_enum_dec (dsl : decl_specifier list) =
    case dsl of
      [] => NONE
    | TypeSpec (Tsenum es) :: rest => if null (#2 (node es)) then
                                        first_enum_dec rest
                                      else SOME es
    | _ :: rest => first_enum_dec rest

fun wonky_pdec_check ctxt dsl = let
  val _ =
      case has_typedef dsl of
        NONE => ()
      | SOME (l,r) => errorStr' ctxt (l, r, "Typedefs forbidden in parameters")
  val _ =
      case has_extern dsl of
        NONE => ()
      | SOME (l,r) => errorStr' ctxt (l,r, "Extern forbidden in parameters")
  val _ = case first_sdecls (node dsl) of
            [] => ()
          | sd :: _ => let
              val sw = #1 (node sd)
            in
              errorStr' ctxt (left sw, right sw,
                         "Don't declare structs / unions in parameters")
            end
  val _ = case first_enum_dec (node dsl) of
            NONE => ()
          | SOME es  => errorStr' ctxt (left es, right es,
                                  "Don't declare enumerations in parameters")
in
  ()
end

fun unwrap_params pms =
    map (fn w => apsnd (Option.map node) (node w)) (the pms)


(* is not a function definition, is at least one declarator
   This means this could be a
     a) list of variable/function declarations (initialised or not)
     b) list of typedefs
 *)
fun make_declaration ctxt (dsl : decl_specifier list wrap)
                     (idl : (addecl wrap * initializer option) wrap list) =
let
  val basetype = extract_type ctxt dsl
  val is_typedef = is_some (has_typedef dsl)
  val is_extern = is_some (has_extern dsl)
  val sdecls = tag_first_sdecls (node dsl)
  val endecs = case first_enum_dec (node dsl) of
                 NONE => []
               | SOME es => [wrap(EnumDecl (node es), left es, right es)]
  val fnspecs = extract_fnspecs (node dsl)
  val storage_specs = extract_storage_specs (node dsl)
  val fnspec_attrs = extract_fnspec_attrs fnspecs

  fun handle_declarator idw = let
    val (d : addecl wrap, iopt : initializer option) = node idw
    val (nm, a : adecl, params, attrs) = node d
    val finaltype = (node a) (node basetype)
  in
    if is_typedef then let
        val _ = case iopt of
                  SOME i => errorStr' ctxt (left idw, right idw,
                                      "Can't initialise a typedef")
                | _ => ()
      in
        wrap(TypeDecl[(finaltype,nm)], left idw, right idw)
      end
    else
      case finaltype of
        Function(rettype, ptys) => let
          val _ = case iopt of
                    SOME _ => errorStr' ctxt (left idw, right idw,
                                        "Can't initialise a function!")
                  | NONE => ()
        in
          wrap(ExtFnDecl { rettype = rettype, name = nm,
                           params = unwrap_params params,
                           specs = merge_specs [gcc_attribs attrs] fnspecs},
               left idw, right idw)
        end
      | _ => let
          val _ =
              if is_extern andalso is_some iopt then
                errorStr' ctxt (left idw, right idw, "Don't initialise externs")
              else ()
        in
          wrap(VarDecl(finaltype, nm, storage_specs, iopt,
                       fnspec_attrs @ attrs ),
               left idw, right idw)
        end
  end
in
  endecs @
  map handle_declarator idl @
  map (parse_siddecl ctxt) sdecls
end

fun last_blockitem (bilist : block_item list) = let
  val bi = List.last bilist
  fun recurse bi =
    case bi of
      BI_Stmt st => (case snode st of
                       Block bilist => last_blockitem bilist
                     | _ => bi)
    | _ => bi
in
  recurse bi
end

fun CaseEndBI bi =
    case bi of
      BI_Stmt st => CaseEndStmt st
    | BI_Decl d => false
and CaseEndStmt st =
    case snode st of
      Break => true
    | Return _ => true
    | ReturnFnCall _ => true
    | IfStmt(g, t, e) => CaseEndStmt t andalso CaseEndStmt e
    | Block bilist => CaseEndBI (last_blockitem bilist)
    | _ => false

fun front [] = []
  | front [h] = []
  | front (x::xs) = x :: front xs

fun removelast_if_break bilist = let
  fun singcase bi =
      case bi of
        BI_Stmt st => let
        in
          case snode st of
            Break => []
          | Block bilist => [BI_Stmt
                                 (swrap (Block (removelast_if_break bilist),
                                         sleft st, sright st))]
          | _ => [bi]
        end
      | _ => [bi]
in
  case bilist of
    [] => []
  | [bi] => singcase bi
  | bi :: bis => bi :: removelast_if_break bis
end

fun mk_defaultcase_last ctxt caselist = let
  fun extract_default caselist =
      case caselist of
        [] => (NONE, [])
      | (c as (labs, bilist)) :: rest => let
          fun is_dflt lab =
              case node lab of
                NONE => true
              | _ => false
        in
          case List.find is_dflt (node labs) of
            NONE => let
              val (df, rest) = extract_default rest
            in
              (df, c::rest)
            end
          | SOME d => let
            in
              if length (node labs) > 1 then
                warnStr' ctxt (left d, right d,
                         "This default: label should be the only label\
                         \ associated with this case")
              else ();
              (SOME (wrap([d], left labs, right labs), bilist), rest)
            end
        end
  val (dflt, rest) = extract_default caselist
in
  case dflt of
    NONE => caselist @ [(bogwrap [bogwrap NONE],
                         [BI_Stmt (swrap(EmptyStmt, bogus, bogus))])]
  | SOME d => rest @ [d]
end


fun switch_check ctxt scaselist leftp rightp = let
  val _ = case length scaselist of
            0 => errorStr' ctxt (leftp, rightp, "Switch has no cases")
          | 1 => errorStr' ctxt (leftp, rightp, "Switch has only one case")
          | _ => ()
  fun check_for_breaks (labs, bilist) =
      if not (CaseEndBI (last_blockitem bilist)) then
        errorStr' ctxt (left labs, right labs,
                  "Switch case beginning here does not end with a break \
                  \or return")
      else ()
  val _ = app check_for_breaks (front scaselist)
          (* only check front of list, allowing for last case to fall through
             to end without a break *)
  val scaselist = mk_defaultcase_last ctxt scaselist
  fun striplabwrap (lab : expr option wrap) = node lab
  fun striplablist llist = map striplabwrap (node llist)
in
  map (fn (labs,bod) => (striplablist labs, removelast_if_break bod)) scaselist
end


fun check_for_proto ctxt d = let
  val dec = node d
in
  case dec of
    ExtFnDecl _ => (errorStr' ctxt (left d, right d,
                              "Don't put function prototypes other than at \
                              \top level"); d)
  | _ => d
end


end
structure LrTable = Token.LrTable
structure Token = Token
local open LrTable in 
val table=let val actionRows =
"\
\\001\000\001\000\000\000\000\000\
\\001\000\001\000\013\002\000\000\
\\001\000\001\000\014\002\012\000\048\000\035\000\047\000\049\000\046\000\
\\063\000\045\000\064\000\044\000\065\000\043\000\066\000\042\000\
\\067\000\041\000\068\000\040\000\069\000\039\000\070\000\038\000\
\\071\000\037\000\074\000\036\000\076\000\035\000\077\000\034\000\
\\078\000\033\000\079\000\032\000\080\000\031\000\081\000\030\000\
\\082\000\029\000\084\000\028\000\085\000\027\000\086\000\026\000\
\\087\000\025\000\088\000\024\000\089\000\023\000\090\000\022\000\
\\093\000\021\000\095\000\020\000\098\000\019\000\101\000\018\000\
\\103\000\017\000\000\000\
\\001\000\001\000\015\002\000\000\
\\001\000\001\000\016\002\012\000\016\002\035\000\016\002\049\000\016\002\
\\063\000\016\002\064\000\016\002\065\000\016\002\066\000\016\002\
\\067\000\016\002\068\000\016\002\069\000\016\002\070\000\016\002\
\\071\000\016\002\074\000\016\002\076\000\016\002\077\000\016\002\
\\078\000\016\002\079\000\016\002\080\000\016\002\081\000\016\002\
\\082\000\016\002\084\000\016\002\085\000\016\002\086\000\016\002\
\\087\000\016\002\088\000\016\002\089\000\016\002\090\000\016\002\
\\093\000\016\002\095\000\016\002\098\000\016\002\101\000\016\002\
\\103\000\016\002\000\000\
\\001\000\001\000\017\002\012\000\017\002\035\000\017\002\049\000\017\002\
\\063\000\017\002\064\000\017\002\065\000\017\002\066\000\017\002\
\\067\000\017\002\068\000\017\002\069\000\017\002\070\000\017\002\
\\071\000\017\002\074\000\017\002\076\000\017\002\077\000\017\002\
\\078\000\017\002\079\000\017\002\080\000\017\002\081\000\017\002\
\\082\000\017\002\084\000\017\002\085\000\017\002\086\000\017\002\
\\087\000\017\002\088\000\017\002\089\000\017\002\090\000\017\002\
\\093\000\017\002\095\000\017\002\098\000\017\002\101\000\017\002\
\\103\000\017\002\000\000\
\\001\000\001\000\018\002\012\000\018\002\035\000\018\002\049\000\018\002\
\\063\000\018\002\064\000\018\002\065\000\018\002\066\000\018\002\
\\067\000\018\002\068\000\018\002\069\000\018\002\070\000\018\002\
\\071\000\018\002\074\000\018\002\076\000\018\002\077\000\018\002\
\\078\000\018\002\079\000\018\002\080\000\018\002\081\000\018\002\
\\082\000\018\002\084\000\018\002\085\000\018\002\086\000\018\002\
\\087\000\018\002\088\000\018\002\089\000\018\002\090\000\018\002\
\\093\000\018\002\095\000\018\002\098\000\018\002\101\000\018\002\
\\103\000\018\002\000\000\
\\001\000\001\000\052\002\002\000\052\002\005\000\052\002\007\000\052\002\
\\008\000\052\002\012\000\052\002\018\000\052\002\020\000\052\002\
\\021\000\052\002\022\000\052\002\035\000\052\002\036\000\052\002\
\\038\000\052\002\039\000\052\002\040\000\052\002\041\000\052\002\
\\042\000\052\002\043\000\052\002\044\000\052\002\045\000\052\002\
\\046\000\052\002\047\000\052\002\048\000\052\002\049\000\052\002\
\\050\000\052\002\063\000\052\002\064\000\052\002\065\000\052\002\
\\066\000\052\002\067\000\052\002\068\000\052\002\069\000\052\002\
\\070\000\052\002\071\000\052\002\073\000\052\002\074\000\052\002\
\\075\000\052\002\076\000\052\002\077\000\052\002\078\000\052\002\
\\079\000\052\002\080\000\052\002\081\000\052\002\082\000\052\002\
\\084\000\052\002\085\000\052\002\086\000\052\002\087\000\052\002\
\\088\000\052\002\089\000\052\002\090\000\052\002\091\000\052\002\
\\092\000\052\002\093\000\052\002\095\000\052\002\096\000\052\002\
\\098\000\052\002\099\000\052\002\101\000\052\002\102\000\052\002\
\\103\000\052\002\000\000\
\\001\000\001\000\053\002\002\000\053\002\005\000\053\002\007\000\053\002\
\\008\000\053\002\012\000\053\002\018\000\053\002\020\000\053\002\
\\021\000\053\002\022\000\053\002\035\000\053\002\036\000\053\002\
\\038\000\053\002\039\000\053\002\040\000\053\002\041\000\053\002\
\\042\000\053\002\043\000\053\002\044\000\053\002\045\000\053\002\
\\046\000\053\002\047\000\053\002\048\000\053\002\049\000\053\002\
\\050\000\053\002\063\000\053\002\064\000\053\002\065\000\053\002\
\\066\000\053\002\067\000\053\002\068\000\053\002\069\000\053\002\
\\070\000\053\002\071\000\053\002\073\000\053\002\074\000\053\002\
\\075\000\053\002\076\000\053\002\077\000\053\002\078\000\053\002\
\\079\000\053\002\080\000\053\002\081\000\053\002\082\000\053\002\
\\084\000\053\002\085\000\053\002\086\000\053\002\087\000\053\002\
\\088\000\053\002\089\000\053\002\090\000\053\002\091\000\053\002\
\\092\000\053\002\093\000\053\002\095\000\053\002\096\000\053\002\
\\098\000\053\002\099\000\053\002\101\000\053\002\102\000\053\002\
\\103\000\053\002\000\000\
\\001\000\001\000\062\002\012\000\062\002\035\000\062\002\049\000\062\002\
\\063\000\062\002\064\000\062\002\065\000\062\002\066\000\062\002\
\\067\000\062\002\068\000\062\002\069\000\062\002\070\000\062\002\
\\071\000\062\002\074\000\062\002\076\000\062\002\077\000\062\002\
\\078\000\062\002\079\000\062\002\080\000\062\002\081\000\062\002\
\\082\000\062\002\084\000\062\002\085\000\062\002\086\000\062\002\
\\087\000\062\002\088\000\062\002\089\000\062\002\090\000\062\002\
\\093\000\062\002\095\000\062\002\098\000\062\002\101\000\062\002\
\\103\000\062\002\000\000\
\\001\000\001\000\070\002\002\000\070\002\005\000\070\002\007\000\070\002\
\\008\000\070\002\012\000\070\002\018\000\070\002\020\000\070\002\
\\021\000\070\002\022\000\070\002\035\000\070\002\036\000\070\002\
\\037\000\070\002\038\000\070\002\039\000\070\002\040\000\070\002\
\\041\000\070\002\042\000\070\002\043\000\070\002\044\000\070\002\
\\045\000\070\002\046\000\070\002\047\000\070\002\048\000\070\002\
\\049\000\070\002\050\000\070\002\063\000\070\002\064\000\070\002\
\\065\000\070\002\066\000\070\002\067\000\070\002\068\000\070\002\
\\069\000\070\002\070\000\070\002\071\000\070\002\073\000\070\002\
\\074\000\070\002\075\000\070\002\076\000\070\002\077\000\070\002\
\\078\000\070\002\079\000\070\002\080\000\070\002\081\000\070\002\
\\082\000\070\002\084\000\070\002\085\000\070\002\086\000\070\002\
\\087\000\070\002\088\000\070\002\089\000\070\002\090\000\070\002\
\\091\000\070\002\092\000\070\002\093\000\070\002\095\000\070\002\
\\096\000\070\002\097\000\070\002\098\000\070\002\099\000\070\002\
\\101\000\070\002\102\000\070\002\103\000\070\002\000\000\
\\001\000\002\000\019\002\005\000\019\002\006\000\019\002\009\000\019\002\
\\011\000\019\002\012\000\019\002\035\000\019\002\049\000\019\002\
\\063\000\019\002\064\000\019\002\065\000\019\002\066\000\019\002\
\\067\000\019\002\068\000\019\002\069\000\019\002\070\000\019\002\
\\071\000\019\002\073\000\019\002\074\000\019\002\076\000\019\002\
\\077\000\019\002\078\000\019\002\079\000\019\002\080\000\019\002\
\\081\000\019\002\082\000\019\002\084\000\019\002\085\000\019\002\
\\086\000\019\002\087\000\019\002\088\000\019\002\089\000\019\002\
\\090\000\019\002\093\000\019\002\095\000\019\002\098\000\019\002\
\\101\000\019\002\103\000\019\002\000\000\
\\001\000\002\000\020\002\005\000\020\002\006\000\020\002\009\000\020\002\
\\011\000\020\002\012\000\020\002\035\000\020\002\049\000\020\002\
\\063\000\020\002\064\000\020\002\065\000\020\002\066\000\020\002\
\\067\000\020\002\068\000\020\002\069\000\020\002\070\000\020\002\
\\071\000\020\002\073\000\020\002\074\000\020\002\076\000\020\002\
\\077\000\020\002\078\000\020\002\079\000\020\002\080\000\020\002\
\\081\000\020\002\082\000\020\002\084\000\020\002\085\000\020\002\
\\086\000\020\002\087\000\020\002\088\000\020\002\089\000\020\002\
\\090\000\020\002\093\000\020\002\095\000\020\002\098\000\020\002\
\\101\000\020\002\103\000\020\002\000\000\
\\001\000\002\000\021\002\005\000\021\002\006\000\021\002\009\000\021\002\
\\011\000\021\002\012\000\021\002\035\000\021\002\049\000\021\002\
\\063\000\021\002\064\000\021\002\065\000\021\002\066\000\021\002\
\\067\000\021\002\068\000\021\002\069\000\021\002\070\000\021\002\
\\071\000\021\002\073\000\021\002\074\000\021\002\076\000\021\002\
\\077\000\021\002\078\000\021\002\079\000\021\002\080\000\021\002\
\\081\000\021\002\082\000\021\002\084\000\021\002\085\000\021\002\
\\086\000\021\002\087\000\021\002\088\000\021\002\089\000\021\002\
\\090\000\021\002\093\000\021\002\095\000\021\002\098\000\021\002\
\\101\000\021\002\103\000\021\002\000\000\
\\001\000\002\000\022\002\005\000\022\002\006\000\022\002\009\000\022\002\
\\011\000\022\002\012\000\022\002\035\000\022\002\049\000\022\002\
\\063\000\022\002\064\000\022\002\065\000\022\002\066\000\022\002\
\\067\000\022\002\068\000\022\002\069\000\022\002\070\000\022\002\
\\071\000\022\002\073\000\022\002\074\000\022\002\076\000\022\002\
\\077\000\022\002\078\000\022\002\079\000\022\002\080\000\022\002\
\\081\000\022\002\082\000\022\002\084\000\022\002\085\000\022\002\
\\086\000\022\002\087\000\022\002\088\000\022\002\089\000\022\002\
\\090\000\022\002\093\000\022\002\095\000\022\002\098\000\022\002\
\\101\000\022\002\103\000\022\002\000\000\
\\001\000\002\000\023\002\005\000\023\002\006\000\023\002\009\000\023\002\
\\011\000\023\002\012\000\023\002\035\000\023\002\049\000\023\002\
\\063\000\023\002\064\000\023\002\065\000\023\002\066\000\023\002\
\\067\000\023\002\068\000\023\002\069\000\023\002\070\000\023\002\
\\071\000\023\002\073\000\023\002\074\000\023\002\076\000\023\002\
\\077\000\023\002\078\000\023\002\079\000\023\002\080\000\023\002\
\\081\000\023\002\082\000\023\002\084\000\023\002\085\000\023\002\
\\086\000\023\002\087\000\023\002\088\000\023\002\089\000\023\002\
\\090\000\023\002\093\000\023\002\095\000\023\002\098\000\023\002\
\\101\000\023\002\103\000\023\002\000\000\
\\001\000\002\000\024\002\005\000\024\002\006\000\024\002\009\000\024\002\
\\011\000\024\002\012\000\024\002\035\000\024\002\049\000\024\002\
\\063\000\024\002\064\000\024\002\065\000\024\002\066\000\024\002\
\\067\000\024\002\068\000\024\002\069\000\024\002\070\000\024\002\
\\071\000\024\002\073\000\024\002\074\000\024\002\076\000\024\002\
\\077\000\024\002\078\000\024\002\079\000\024\002\080\000\024\002\
\\081\000\024\002\082\000\024\002\084\000\024\002\085\000\024\002\
\\086\000\024\002\087\000\024\002\088\000\024\002\089\000\024\002\
\\090\000\024\002\093\000\024\002\095\000\024\002\098\000\024\002\
\\101\000\024\002\103\000\024\002\000\000\
\\001\000\002\000\025\002\005\000\025\002\006\000\025\002\009\000\025\002\
\\011\000\025\002\012\000\025\002\035\000\025\002\049\000\025\002\
\\063\000\025\002\064\000\025\002\065\000\025\002\066\000\025\002\
\\067\000\025\002\068\000\025\002\069\000\025\002\070\000\025\002\
\\071\000\025\002\073\000\025\002\074\000\025\002\076\000\025\002\
\\077\000\025\002\078\000\025\002\079\000\025\002\080\000\025\002\
\\081\000\025\002\082\000\025\002\084\000\025\002\085\000\025\002\
\\086\000\025\002\087\000\025\002\088\000\025\002\089\000\025\002\
\\090\000\025\002\093\000\025\002\095\000\025\002\098\000\025\002\
\\101\000\025\002\103\000\025\002\000\000\
\\001\000\002\000\026\002\005\000\026\002\006\000\026\002\009\000\026\002\
\\011\000\026\002\012\000\026\002\035\000\026\002\049\000\026\002\
\\063\000\026\002\064\000\026\002\065\000\026\002\066\000\026\002\
\\067\000\026\002\068\000\026\002\069\000\026\002\070\000\026\002\
\\071\000\026\002\073\000\026\002\074\000\026\002\076\000\026\002\
\\077\000\026\002\078\000\026\002\079\000\026\002\080\000\026\002\
\\081\000\026\002\082\000\026\002\084\000\026\002\085\000\026\002\
\\086\000\026\002\087\000\026\002\088\000\026\002\089\000\026\002\
\\090\000\026\002\093\000\026\002\095\000\026\002\098\000\026\002\
\\101\000\026\002\103\000\026\002\000\000\
\\001\000\002\000\027\002\005\000\027\002\006\000\027\002\009\000\027\002\
\\011\000\027\002\012\000\027\002\035\000\027\002\049\000\027\002\
\\063\000\027\002\064\000\027\002\065\000\027\002\066\000\027\002\
\\067\000\027\002\068\000\027\002\069\000\027\002\070\000\027\002\
\\071\000\027\002\073\000\027\002\074\000\027\002\076\000\027\002\
\\077\000\027\002\078\000\027\002\079\000\027\002\080\000\027\002\
\\081\000\027\002\082\000\027\002\084\000\027\002\085\000\027\002\
\\086\000\027\002\087\000\027\002\088\000\027\002\089\000\027\002\
\\090\000\027\002\093\000\027\002\095\000\027\002\098\000\027\002\
\\101\000\027\002\103\000\027\002\000\000\
\\001\000\002\000\028\002\005\000\028\002\006\000\028\002\009\000\028\002\
\\011\000\028\002\012\000\028\002\035\000\028\002\049\000\028\002\
\\063\000\028\002\064\000\028\002\065\000\028\002\066\000\028\002\
\\067\000\028\002\068\000\028\002\069\000\028\002\070\000\028\002\
\\071\000\028\002\073\000\028\002\074\000\028\002\076\000\028\002\
\\077\000\028\002\078\000\028\002\079\000\028\002\080\000\028\002\
\\081\000\028\002\082\000\028\002\084\000\028\002\085\000\028\002\
\\086\000\028\002\087\000\028\002\088\000\028\002\089\000\028\002\
\\090\000\028\002\093\000\028\002\095\000\028\002\098\000\028\002\
\\101\000\028\002\103\000\028\002\000\000\
\\001\000\002\000\029\002\005\000\029\002\006\000\029\002\007\000\029\002\
\\009\000\029\002\011\000\029\002\012\000\029\002\013\000\029\002\
\\015\000\029\002\035\000\029\002\049\000\029\002\063\000\029\002\
\\064\000\029\002\065\000\029\002\066\000\029\002\067\000\029\002\
\\068\000\029\002\069\000\029\002\070\000\029\002\071\000\029\002\
\\073\000\029\002\074\000\029\002\076\000\029\002\077\000\029\002\
\\078\000\029\002\079\000\029\002\080\000\029\002\081\000\029\002\
\\082\000\029\002\084\000\029\002\085\000\029\002\086\000\029\002\
\\087\000\029\002\088\000\029\002\089\000\029\002\090\000\029\002\
\\093\000\029\002\095\000\029\002\098\000\029\002\101\000\029\002\
\\102\000\029\002\103\000\029\002\000\000\
\\001\000\002\000\030\002\005\000\030\002\006\000\030\002\007\000\030\002\
\\009\000\030\002\011\000\030\002\012\000\030\002\013\000\030\002\
\\015\000\030\002\035\000\030\002\049\000\030\002\063\000\030\002\
\\064\000\030\002\065\000\030\002\066\000\030\002\067\000\030\002\
\\068\000\030\002\069\000\030\002\070\000\030\002\071\000\030\002\
\\073\000\030\002\074\000\030\002\076\000\030\002\077\000\030\002\
\\078\000\030\002\079\000\030\002\080\000\030\002\081\000\030\002\
\\082\000\030\002\084\000\030\002\085\000\030\002\086\000\030\002\
\\087\000\030\002\088\000\030\002\089\000\030\002\090\000\030\002\
\\093\000\030\002\095\000\030\002\098\000\030\002\101\000\030\002\
\\102\000\030\002\103\000\030\002\000\000\
\\001\000\002\000\054\002\005\000\054\002\006\000\054\002\009\000\054\002\
\\011\000\054\002\012\000\054\002\035\000\047\000\049\000\046\000\
\\063\000\045\000\064\000\044\000\065\000\043\000\066\000\042\000\
\\067\000\041\000\068\000\040\000\069\000\039\000\070\000\038\000\
\\071\000\037\000\073\000\054\002\074\000\036\000\076\000\035\000\
\\077\000\034\000\078\000\033\000\079\000\032\000\080\000\031\000\
\\081\000\030\000\082\000\029\000\084\000\028\000\085\000\027\000\
\\086\000\026\000\087\000\025\000\088\000\024\000\089\000\023\000\
\\090\000\022\000\093\000\021\000\095\000\020\000\098\000\019\000\
\\101\000\018\000\103\000\017\000\000\000\
\\001\000\002\000\055\002\005\000\055\002\006\000\055\002\009\000\055\002\
\\011\000\055\002\012\000\055\002\073\000\055\002\000\000\
\\001\000\002\000\056\002\005\000\056\002\006\000\056\002\009\000\056\002\
\\011\000\056\002\012\000\056\002\035\000\047\000\049\000\046\000\
\\063\000\045\000\064\000\044\000\065\000\043\000\066\000\042\000\
\\067\000\041\000\068\000\040\000\069\000\039\000\070\000\038\000\
\\071\000\037\000\073\000\056\002\074\000\036\000\076\000\035\000\
\\077\000\034\000\078\000\033\000\079\000\032\000\080\000\031\000\
\\081\000\030\000\082\000\029\000\084\000\028\000\085\000\027\000\
\\086\000\026\000\087\000\025\000\088\000\024\000\089\000\023\000\
\\090\000\022\000\093\000\021\000\095\000\020\000\098\000\019\000\
\\101\000\018\000\103\000\017\000\000\000\
\\001\000\002\000\057\002\005\000\057\002\006\000\057\002\009\000\057\002\
\\011\000\057\002\012\000\057\002\073\000\057\002\000\000\
\\001\000\002\000\058\002\005\000\058\002\006\000\058\002\009\000\058\002\
\\011\000\058\002\012\000\058\002\035\000\047\000\049\000\046\000\
\\063\000\045\000\064\000\044\000\065\000\043\000\066\000\042\000\
\\067\000\041\000\068\000\040\000\069\000\039\000\070\000\038\000\
\\071\000\037\000\073\000\058\002\074\000\036\000\076\000\035\000\
\\077\000\034\000\078\000\033\000\079\000\032\000\080\000\031\000\
\\081\000\030\000\082\000\029\000\084\000\028\000\085\000\027\000\
\\086\000\026\000\087\000\025\000\088\000\024\000\089\000\023\000\
\\090\000\022\000\093\000\021\000\095\000\020\000\098\000\019\000\
\\101\000\018\000\103\000\017\000\000\000\
\\001\000\002\000\059\002\005\000\059\002\006\000\059\002\009\000\059\002\
\\011\000\059\002\012\000\059\002\073\000\059\002\000\000\
\\001\000\002\000\060\002\005\000\060\002\006\000\060\002\009\000\060\002\
\\011\000\060\002\012\000\060\002\035\000\047\000\049\000\046\000\
\\063\000\045\000\064\000\044\000\065\000\043\000\066\000\042\000\
\\067\000\041\000\068\000\040\000\069\000\039\000\070\000\038\000\
\\071\000\037\000\073\000\060\002\074\000\036\000\076\000\035\000\
\\077\000\034\000\078\000\033\000\079\000\032\000\080\000\031\000\
\\081\000\030\000\082\000\029\000\084\000\028\000\085\000\027\000\
\\086\000\026\000\087\000\025\000\088\000\024\000\089\000\023\000\
\\090\000\022\000\093\000\021\000\095\000\020\000\098\000\019\000\
\\101\000\018\000\103\000\017\000\000\000\
\\001\000\002\000\061\002\005\000\061\002\006\000\061\002\009\000\061\002\
\\011\000\061\002\012\000\061\002\073\000\061\002\000\000\
\\001\000\002\000\073\002\005\000\073\002\007\000\073\002\008\000\073\002\
\\012\000\073\002\018\000\073\002\020\000\073\002\021\000\073\002\
\\022\000\073\002\035\000\073\002\036\000\073\002\038\000\073\002\
\\039\000\073\002\040\000\073\002\041\000\073\002\042\000\073\002\
\\043\000\073\002\044\000\073\002\045\000\073\002\046\000\073\002\
\\047\000\073\002\048\000\073\002\049\000\073\002\050\000\073\002\
\\063\000\073\002\064\000\073\002\065\000\073\002\066\000\073\002\
\\067\000\073\002\068\000\073\002\069\000\073\002\070\000\073\002\
\\071\000\073\002\073\000\073\002\074\000\073\002\075\000\073\002\
\\076\000\073\002\077\000\073\002\078\000\073\002\079\000\073\002\
\\080\000\073\002\081\000\073\002\082\000\073\002\084\000\073\002\
\\085\000\073\002\086\000\073\002\087\000\073\002\088\000\073\002\
\\089\000\073\002\090\000\073\002\091\000\073\002\092\000\073\002\
\\093\000\073\002\095\000\073\002\096\000\073\002\098\000\073\002\
\\099\000\073\002\101\000\073\002\102\000\073\002\103\000\073\002\000\000\
\\001\000\002\000\074\002\005\000\074\002\007\000\074\002\008\000\074\002\
\\012\000\074\002\018\000\074\002\020\000\074\002\021\000\074\002\
\\022\000\074\002\035\000\074\002\036\000\074\002\038\000\074\002\
\\039\000\074\002\040\000\074\002\041\000\074\002\042\000\074\002\
\\043\000\074\002\044\000\074\002\045\000\074\002\046\000\074\002\
\\047\000\074\002\048\000\074\002\049\000\074\002\050\000\074\002\
\\063\000\074\002\064\000\074\002\065\000\074\002\066\000\074\002\
\\067\000\074\002\068\000\074\002\069\000\074\002\070\000\074\002\
\\071\000\074\002\073\000\074\002\074\000\074\002\075\000\074\002\
\\076\000\074\002\077\000\074\002\078\000\074\002\079\000\074\002\
\\080\000\074\002\081\000\074\002\082\000\074\002\084\000\074\002\
\\085\000\074\002\086\000\074\002\087\000\074\002\088\000\074\002\
\\089\000\074\002\090\000\074\002\091\000\074\002\092\000\074\002\
\\093\000\074\002\095\000\074\002\096\000\074\002\098\000\074\002\
\\099\000\074\002\101\000\074\002\102\000\074\002\103\000\074\002\000\000\
\\001\000\002\000\081\002\005\000\081\002\006\000\081\002\009\000\081\002\
\\035\000\047\000\049\000\046\000\063\000\045\000\064\000\044\000\
\\065\000\043\000\066\000\042\000\067\000\041\000\068\000\040\000\
\\069\000\039\000\070\000\038\000\071\000\037\000\073\000\081\002\
\\074\000\036\000\076\000\035\000\077\000\034\000\080\000\031\000\
\\081\000\030\000\082\000\029\000\000\000\
\\001\000\002\000\082\002\005\000\082\002\006\000\082\002\009\000\082\002\
\\073\000\082\002\000\000\
\\001\000\002\000\083\002\005\000\083\002\006\000\083\002\009\000\083\002\
\\035\000\047\000\049\000\046\000\063\000\045\000\064\000\044\000\
\\065\000\043\000\066\000\042\000\067\000\041\000\068\000\040\000\
\\069\000\039\000\070\000\038\000\071\000\037\000\073\000\083\002\
\\074\000\036\000\076\000\035\000\077\000\034\000\080\000\031\000\
\\081\000\030\000\082\000\029\000\000\000\
\\001\000\002\000\084\002\005\000\084\002\006\000\084\002\009\000\084\002\
\\073\000\084\002\000\000\
\\001\000\002\000\085\002\005\000\085\002\006\000\085\002\009\000\085\002\
\\011\000\085\002\012\000\085\002\035\000\085\002\049\000\085\002\
\\063\000\085\002\064\000\085\002\065\000\085\002\066\000\085\002\
\\067\000\085\002\068\000\085\002\069\000\085\002\070\000\085\002\
\\071\000\085\002\073\000\085\002\074\000\085\002\076\000\085\002\
\\077\000\085\002\078\000\085\002\079\000\085\002\080\000\085\002\
\\081\000\085\002\082\000\085\002\084\000\085\002\085\000\085\002\
\\086\000\085\002\087\000\085\002\088\000\085\002\089\000\085\002\
\\090\000\085\002\093\000\085\002\095\000\085\002\098\000\085\002\
\\101\000\085\002\103\000\085\002\000\000\
\\001\000\002\000\086\002\005\000\086\002\006\000\086\002\009\000\086\002\
\\011\000\086\002\012\000\086\002\035\000\086\002\049\000\086\002\
\\063\000\086\002\064\000\086\002\065\000\086\002\066\000\086\002\
\\067\000\086\002\068\000\086\002\069\000\086\002\070\000\086\002\
\\071\000\086\002\073\000\086\002\074\000\086\002\076\000\086\002\
\\077\000\086\002\078\000\086\002\079\000\086\002\080\000\086\002\
\\081\000\086\002\082\000\086\002\084\000\086\002\085\000\086\002\
\\086\000\086\002\087\000\086\002\088\000\086\002\089\000\086\002\
\\090\000\086\002\093\000\086\002\095\000\086\002\098\000\086\002\
\\101\000\086\002\103\000\086\002\000\000\
\\001\000\002\000\087\002\005\000\087\002\006\000\087\002\009\000\087\002\
\\011\000\087\002\012\000\087\002\035\000\087\002\049\000\087\002\
\\063\000\087\002\064\000\087\002\065\000\087\002\066\000\087\002\
\\067\000\087\002\068\000\087\002\069\000\087\002\070\000\087\002\
\\071\000\087\002\073\000\087\002\074\000\087\002\076\000\087\002\
\\077\000\087\002\078\000\087\002\079\000\087\002\080\000\087\002\
\\081\000\087\002\082\000\087\002\084\000\087\002\085\000\087\002\
\\086\000\087\002\087\000\087\002\088\000\087\002\089\000\087\002\
\\090\000\087\002\093\000\087\002\095\000\087\002\098\000\087\002\
\\101\000\087\002\103\000\087\002\000\000\
\\001\000\002\000\088\002\005\000\088\002\006\000\088\002\009\000\088\002\
\\011\000\088\002\073\000\088\002\080\000\031\000\081\000\030\000\
\\082\000\029\000\095\000\088\002\101\000\088\002\000\000\
\\001\000\002\000\089\002\005\000\089\002\006\000\089\002\009\000\089\002\
\\011\000\089\002\073\000\089\002\095\000\089\002\101\000\089\002\000\000\
\\001\000\002\000\116\002\005\000\116\002\006\000\116\002\007\000\116\002\
\\009\000\116\002\011\000\116\002\012\000\116\002\035\000\116\002\
\\049\000\116\002\063\000\116\002\064\000\116\002\065\000\116\002\
\\066\000\116\002\067\000\116\002\068\000\116\002\069\000\116\002\
\\070\000\116\002\071\000\116\002\073\000\116\002\074\000\116\002\
\\076\000\116\002\077\000\116\002\078\000\116\002\079\000\116\002\
\\080\000\116\002\081\000\116\002\082\000\116\002\084\000\116\002\
\\085\000\116\002\086\000\116\002\087\000\116\002\088\000\116\002\
\\089\000\116\002\090\000\116\002\093\000\116\002\095\000\116\002\
\\098\000\116\002\101\000\116\002\103\000\116\002\000\000\
\\001\000\002\000\117\002\005\000\117\002\006\000\117\002\007\000\117\002\
\\009\000\117\002\011\000\117\002\012\000\117\002\035\000\117\002\
\\049\000\117\002\063\000\117\002\064\000\117\002\065\000\117\002\
\\066\000\117\002\067\000\117\002\068\000\117\002\069\000\117\002\
\\070\000\117\002\071\000\117\002\073\000\117\002\074\000\117\002\
\\076\000\117\002\077\000\117\002\078\000\117\002\079\000\117\002\
\\080\000\117\002\081\000\117\002\082\000\117\002\084\000\117\002\
\\085\000\117\002\086\000\117\002\087\000\117\002\088\000\117\002\
\\089\000\117\002\090\000\117\002\093\000\117\002\095\000\117\002\
\\098\000\117\002\101\000\117\002\103\000\117\002\000\000\
\\001\000\002\000\118\002\005\000\118\002\006\000\118\002\007\000\110\000\
\\009\000\118\002\011\000\118\002\012\000\118\002\035\000\118\002\
\\049\000\118\002\063\000\118\002\064\000\118\002\065\000\118\002\
\\066\000\118\002\067\000\118\002\068\000\118\002\069\000\118\002\
\\070\000\118\002\071\000\118\002\073\000\118\002\074\000\118\002\
\\076\000\118\002\077\000\118\002\078\000\118\002\079\000\118\002\
\\080\000\118\002\081\000\118\002\082\000\118\002\084\000\118\002\
\\085\000\118\002\086\000\118\002\087\000\118\002\088\000\118\002\
\\089\000\118\002\090\000\118\002\093\000\118\002\095\000\118\002\
\\098\000\118\002\101\000\118\002\103\000\118\002\000\000\
\\001\000\002\000\119\002\005\000\119\002\006\000\119\002\009\000\119\002\
\\011\000\119\002\012\000\119\002\035\000\119\002\049\000\119\002\
\\063\000\119\002\064\000\119\002\065\000\119\002\066\000\119\002\
\\067\000\119\002\068\000\119\002\069\000\119\002\070\000\119\002\
\\071\000\119\002\073\000\119\002\074\000\119\002\076\000\119\002\
\\077\000\119\002\078\000\119\002\079\000\119\002\080\000\119\002\
\\081\000\119\002\082\000\119\002\084\000\119\002\085\000\119\002\
\\086\000\119\002\087\000\119\002\088\000\119\002\089\000\119\002\
\\090\000\119\002\093\000\119\002\095\000\020\000\098\000\119\002\
\\101\000\018\000\103\000\119\002\000\000\
\\001\000\002\000\120\002\005\000\120\002\006\000\120\002\009\000\120\002\
\\011\000\120\002\012\000\120\002\035\000\120\002\049\000\120\002\
\\063\000\120\002\064\000\120\002\065\000\120\002\066\000\120\002\
\\067\000\120\002\068\000\120\002\069\000\120\002\070\000\120\002\
\\071\000\120\002\073\000\120\002\074\000\120\002\076\000\120\002\
\\077\000\120\002\078\000\120\002\079\000\120\002\080\000\120\002\
\\081\000\120\002\082\000\120\002\084\000\120\002\085\000\120\002\
\\086\000\120\002\087\000\120\002\088\000\120\002\089\000\120\002\
\\090\000\120\002\093\000\120\002\095\000\120\002\098\000\120\002\
\\101\000\120\002\103\000\120\002\000\000\
\\001\000\002\000\121\002\005\000\121\002\006\000\121\002\009\000\121\002\
\\011\000\121\002\012\000\121\002\035\000\121\002\049\000\121\002\
\\063\000\121\002\064\000\121\002\065\000\121\002\066\000\121\002\
\\067\000\121\002\068\000\121\002\069\000\121\002\070\000\121\002\
\\071\000\121\002\073\000\121\002\074\000\121\002\076\000\121\002\
\\077\000\121\002\078\000\121\002\079\000\121\002\080\000\121\002\
\\081\000\121\002\082\000\121\002\084\000\121\002\085\000\121\002\
\\086\000\121\002\087\000\121\002\088\000\121\002\089\000\121\002\
\\090\000\121\002\093\000\121\002\095\000\020\000\098\000\121\002\
\\101\000\018\000\103\000\121\002\000\000\
\\001\000\002\000\122\002\005\000\122\002\006\000\122\002\009\000\122\002\
\\011\000\122\002\012\000\122\002\035\000\122\002\049\000\122\002\
\\063\000\122\002\064\000\122\002\065\000\122\002\066\000\122\002\
\\067\000\122\002\068\000\122\002\069\000\122\002\070\000\122\002\
\\071\000\122\002\073\000\122\002\074\000\122\002\076\000\122\002\
\\077\000\122\002\078\000\122\002\079\000\122\002\080\000\122\002\
\\081\000\122\002\082\000\122\002\084\000\122\002\085\000\122\002\
\\086\000\122\002\087\000\122\002\088\000\122\002\089\000\122\002\
\\090\000\122\002\093\000\122\002\095\000\122\002\098\000\122\002\
\\101\000\122\002\103\000\122\002\000\000\
\\001\000\002\000\123\002\005\000\123\002\006\000\123\002\007\000\104\000\
\\009\000\123\002\011\000\123\002\012\000\123\002\035\000\123\002\
\\049\000\123\002\063\000\123\002\064\000\123\002\065\000\123\002\
\\066\000\123\002\067\000\123\002\068\000\123\002\069\000\123\002\
\\070\000\123\002\071\000\123\002\073\000\123\002\074\000\123\002\
\\076\000\123\002\077\000\123\002\078\000\123\002\079\000\123\002\
\\080\000\123\002\081\000\123\002\082\000\123\002\084\000\123\002\
\\085\000\123\002\086\000\123\002\087\000\123\002\088\000\123\002\
\\089\000\123\002\090\000\123\002\093\000\123\002\095\000\123\002\
\\098\000\123\002\101\000\123\002\103\000\123\002\000\000\
\\001\000\002\000\124\002\005\000\124\002\006\000\124\002\009\000\124\002\
\\011\000\124\002\012\000\124\002\035\000\124\002\049\000\124\002\
\\063\000\124\002\064\000\124\002\065\000\124\002\066\000\124\002\
\\067\000\124\002\068\000\124\002\069\000\124\002\070\000\124\002\
\\071\000\124\002\073\000\124\002\074\000\124\002\076\000\124\002\
\\077\000\124\002\078\000\124\002\079\000\124\002\080\000\124\002\
\\081\000\124\002\082\000\124\002\084\000\124\002\085\000\124\002\
\\086\000\124\002\087\000\124\002\088\000\124\002\089\000\124\002\
\\090\000\124\002\093\000\124\002\095\000\020\000\098\000\124\002\
\\101\000\018\000\103\000\124\002\000\000\
\\001\000\002\000\125\002\005\000\125\002\006\000\125\002\009\000\125\002\
\\011\000\125\002\012\000\125\002\035\000\125\002\049\000\125\002\
\\063\000\125\002\064\000\125\002\065\000\125\002\066\000\125\002\
\\067\000\125\002\068\000\125\002\069\000\125\002\070\000\125\002\
\\071\000\125\002\073\000\125\002\074\000\125\002\076\000\125\002\
\\077\000\125\002\078\000\125\002\079\000\125\002\080\000\125\002\
\\081\000\125\002\082\000\125\002\084\000\125\002\085\000\125\002\
\\086\000\125\002\087\000\125\002\088\000\125\002\089\000\125\002\
\\090\000\125\002\093\000\125\002\095\000\125\002\098\000\125\002\
\\101\000\125\002\103\000\125\002\000\000\
\\001\000\002\000\126\002\005\000\126\002\006\000\126\002\009\000\126\002\
\\011\000\126\002\012\000\126\002\035\000\126\002\049\000\126\002\
\\063\000\126\002\064\000\126\002\065\000\126\002\066\000\126\002\
\\067\000\126\002\068\000\126\002\069\000\126\002\070\000\126\002\
\\071\000\126\002\073\000\126\002\074\000\126\002\076\000\126\002\
\\077\000\126\002\078\000\126\002\079\000\126\002\080\000\126\002\
\\081\000\126\002\082\000\126\002\084\000\126\002\085\000\126\002\
\\086\000\126\002\087\000\126\002\088\000\126\002\089\000\126\002\
\\090\000\126\002\093\000\126\002\095\000\020\000\098\000\126\002\
\\101\000\018\000\103\000\126\002\000\000\
\\001\000\002\000\127\002\005\000\127\002\006\000\127\002\009\000\127\002\
\\011\000\127\002\012\000\127\002\035\000\127\002\049\000\127\002\
\\063\000\127\002\064\000\127\002\065\000\127\002\066\000\127\002\
\\067\000\127\002\068\000\127\002\069\000\127\002\070\000\127\002\
\\071\000\127\002\073\000\127\002\074\000\127\002\076\000\127\002\
\\077\000\127\002\078\000\127\002\079\000\127\002\080\000\127\002\
\\081\000\127\002\082\000\127\002\084\000\127\002\085\000\127\002\
\\086\000\127\002\087\000\127\002\088\000\127\002\089\000\127\002\
\\090\000\127\002\093\000\127\002\095\000\127\002\098\000\127\002\
\\101\000\127\002\103\000\127\002\000\000\
\\001\000\002\000\128\002\005\000\128\002\006\000\128\002\009\000\128\002\
\\011\000\128\002\012\000\128\002\035\000\128\002\049\000\128\002\
\\063\000\128\002\064\000\128\002\065\000\128\002\066\000\128\002\
\\067\000\128\002\068\000\128\002\069\000\128\002\070\000\128\002\
\\071\000\128\002\073\000\128\002\074\000\128\002\076\000\128\002\
\\077\000\128\002\078\000\128\002\079\000\128\002\080\000\128\002\
\\081\000\128\002\082\000\128\002\084\000\128\002\085\000\128\002\
\\086\000\128\002\087\000\128\002\088\000\128\002\089\000\128\002\
\\090\000\128\002\093\000\128\002\095\000\128\002\098\000\128\002\
\\101\000\128\002\103\000\128\002\000\000\
\\001\000\002\000\129\002\005\000\129\002\006\000\129\002\009\000\129\002\
\\011\000\129\002\012\000\129\002\035\000\129\002\049\000\129\002\
\\063\000\129\002\064\000\129\002\065\000\129\002\066\000\129\002\
\\067\000\129\002\068\000\129\002\069\000\129\002\070\000\129\002\
\\071\000\129\002\073\000\129\002\074\000\129\002\076\000\129\002\
\\077\000\129\002\078\000\129\002\079\000\129\002\080\000\129\002\
\\081\000\129\002\082\000\129\002\084\000\129\002\085\000\129\002\
\\086\000\129\002\087\000\129\002\088\000\129\002\089\000\129\002\
\\090\000\129\002\093\000\129\002\095\000\129\002\098\000\129\002\
\\101\000\129\002\103\000\129\002\000\000\
\\001\000\002\000\130\002\005\000\130\002\006\000\130\002\009\000\130\002\
\\011\000\130\002\012\000\130\002\035\000\130\002\049\000\130\002\
\\063\000\130\002\064\000\130\002\065\000\130\002\066\000\130\002\
\\067\000\130\002\068\000\130\002\069\000\130\002\070\000\130\002\
\\071\000\130\002\073\000\130\002\074\000\130\002\076\000\130\002\
\\077\000\130\002\078\000\130\002\079\000\130\002\080\000\130\002\
\\081\000\130\002\082\000\130\002\084\000\130\002\085\000\130\002\
\\086\000\130\002\087\000\130\002\088\000\130\002\089\000\130\002\
\\090\000\130\002\093\000\130\002\095\000\130\002\098\000\130\002\
\\101\000\130\002\103\000\130\002\000\000\
\\001\000\002\000\131\002\005\000\131\002\006\000\131\002\009\000\131\002\
\\011\000\131\002\012\000\131\002\035\000\131\002\049\000\131\002\
\\063\000\131\002\064\000\131\002\065\000\131\002\066\000\131\002\
\\067\000\131\002\068\000\131\002\069\000\131\002\070\000\131\002\
\\071\000\131\002\073\000\131\002\074\000\131\002\076\000\131\002\
\\077\000\131\002\078\000\131\002\079\000\131\002\080\000\131\002\
\\081\000\131\002\082\000\131\002\084\000\131\002\085\000\131\002\
\\086\000\131\002\087\000\131\002\088\000\131\002\089\000\131\002\
\\090\000\131\002\093\000\131\002\095\000\131\002\098\000\131\002\
\\101\000\131\002\103\000\131\002\000\000\
\\001\000\002\000\132\002\005\000\132\002\006\000\132\002\009\000\132\002\
\\011\000\132\002\012\000\132\002\035\000\132\002\049\000\132\002\
\\063\000\132\002\064\000\132\002\065\000\132\002\066\000\132\002\
\\067\000\132\002\068\000\132\002\069\000\132\002\070\000\132\002\
\\071\000\132\002\073\000\132\002\074\000\132\002\076\000\132\002\
\\077\000\132\002\078\000\132\002\079\000\132\002\080\000\132\002\
\\081\000\132\002\082\000\132\002\084\000\132\002\085\000\132\002\
\\086\000\132\002\087\000\132\002\088\000\132\002\089\000\132\002\
\\090\000\132\002\093\000\132\002\095\000\132\002\098\000\132\002\
\\101\000\132\002\103\000\132\002\000\000\
\\001\000\002\000\133\002\005\000\133\002\006\000\133\002\009\000\133\002\
\\011\000\133\002\012\000\133\002\035\000\133\002\049\000\133\002\
\\063\000\133\002\064\000\133\002\065\000\133\002\066\000\133\002\
\\067\000\133\002\068\000\133\002\069\000\133\002\070\000\133\002\
\\071\000\133\002\073\000\133\002\074\000\133\002\076\000\133\002\
\\077\000\133\002\078\000\133\002\079\000\133\002\080\000\133\002\
\\081\000\133\002\082\000\133\002\084\000\133\002\085\000\133\002\
\\086\000\133\002\087\000\133\002\088\000\133\002\089\000\133\002\
\\090\000\133\002\093\000\133\002\095\000\133\002\098\000\133\002\
\\101\000\133\002\103\000\133\002\000\000\
\\001\000\002\000\134\002\005\000\134\002\006\000\134\002\009\000\134\002\
\\011\000\134\002\012\000\134\002\035\000\134\002\049\000\134\002\
\\063\000\134\002\064\000\134\002\065\000\134\002\066\000\134\002\
\\067\000\134\002\068\000\134\002\069\000\134\002\070\000\134\002\
\\071\000\134\002\073\000\134\002\074\000\134\002\076\000\134\002\
\\077\000\134\002\078\000\134\002\079\000\134\002\080\000\134\002\
\\081\000\134\002\082\000\134\002\084\000\134\002\085\000\134\002\
\\086\000\134\002\087\000\134\002\088\000\134\002\089\000\134\002\
\\090\000\134\002\093\000\134\002\095\000\134\002\098\000\134\002\
\\101\000\134\002\103\000\134\002\000\000\
\\001\000\002\000\135\002\005\000\135\002\006\000\135\002\009\000\135\002\
\\011\000\135\002\012\000\135\002\035\000\135\002\049\000\135\002\
\\063\000\135\002\064\000\135\002\065\000\135\002\066\000\135\002\
\\067\000\135\002\068\000\135\002\069\000\135\002\070\000\135\002\
\\071\000\135\002\073\000\135\002\074\000\135\002\076\000\135\002\
\\077\000\135\002\078\000\135\002\079\000\135\002\080\000\135\002\
\\081\000\135\002\082\000\135\002\084\000\135\002\085\000\135\002\
\\086\000\135\002\087\000\135\002\088\000\135\002\089\000\135\002\
\\090\000\135\002\093\000\135\002\095\000\135\002\098\000\135\002\
\\101\000\135\002\103\000\135\002\000\000\
\\001\000\002\000\136\002\005\000\136\002\006\000\136\002\009\000\136\002\
\\011\000\136\002\012\000\136\002\035\000\136\002\049\000\136\002\
\\063\000\136\002\064\000\136\002\065\000\136\002\066\000\136\002\
\\067\000\136\002\068\000\136\002\069\000\136\002\070\000\136\002\
\\071\000\136\002\073\000\136\002\074\000\136\002\076\000\136\002\
\\077\000\136\002\078\000\136\002\079\000\136\002\080\000\136\002\
\\081\000\136\002\082\000\136\002\084\000\136\002\085\000\136\002\
\\086\000\136\002\087\000\136\002\088\000\136\002\089\000\136\002\
\\090\000\136\002\093\000\136\002\095\000\136\002\098\000\136\002\
\\101\000\136\002\103\000\136\002\000\000\
\\001\000\002\000\137\002\005\000\137\002\006\000\137\002\009\000\137\002\
\\011\000\137\002\012\000\137\002\035\000\137\002\049\000\137\002\
\\063\000\137\002\064\000\137\002\065\000\137\002\066\000\137\002\
\\067\000\137\002\068\000\137\002\069\000\137\002\070\000\137\002\
\\071\000\137\002\073\000\137\002\074\000\137\002\076\000\137\002\
\\077\000\137\002\078\000\137\002\079\000\137\002\080\000\137\002\
\\081\000\137\002\082\000\137\002\084\000\137\002\085\000\137\002\
\\086\000\137\002\087\000\137\002\088\000\137\002\089\000\137\002\
\\090\000\137\002\093\000\137\002\095\000\137\002\098\000\137\002\
\\101\000\137\002\103\000\137\002\000\000\
\\001\000\002\000\138\002\005\000\138\002\006\000\138\002\009\000\138\002\
\\011\000\138\002\012\000\138\002\035\000\138\002\049\000\138\002\
\\063\000\138\002\064\000\138\002\065\000\138\002\066\000\138\002\
\\067\000\138\002\068\000\138\002\069\000\138\002\070\000\138\002\
\\071\000\138\002\073\000\138\002\074\000\138\002\076\000\138\002\
\\077\000\138\002\078\000\138\002\079\000\138\002\080\000\138\002\
\\081\000\138\002\082\000\138\002\084\000\138\002\085\000\138\002\
\\086\000\138\002\087\000\138\002\088\000\138\002\089\000\138\002\
\\090\000\138\002\093\000\138\002\095\000\138\002\098\000\138\002\
\\101\000\138\002\103\000\138\002\000\000\
\\001\000\002\000\139\002\005\000\139\002\006\000\139\002\009\000\139\002\
\\011\000\139\002\012\000\139\002\035\000\139\002\049\000\139\002\
\\063\000\139\002\064\000\139\002\065\000\139\002\066\000\139\002\
\\067\000\139\002\068\000\139\002\069\000\139\002\070\000\139\002\
\\071\000\139\002\073\000\139\002\074\000\139\002\076\000\139\002\
\\077\000\139\002\078\000\139\002\079\000\139\002\080\000\139\002\
\\081\000\139\002\082\000\139\002\084\000\139\002\085\000\139\002\
\\086\000\139\002\087\000\139\002\088\000\139\002\089\000\139\002\
\\090\000\139\002\093\000\139\002\095\000\139\002\098\000\139\002\
\\101\000\139\002\103\000\139\002\000\000\
\\001\000\002\000\140\002\005\000\140\002\006\000\140\002\009\000\140\002\
\\011\000\140\002\012\000\140\002\035\000\140\002\049\000\140\002\
\\063\000\140\002\064\000\140\002\065\000\140\002\066\000\140\002\
\\067\000\140\002\068\000\140\002\069\000\140\002\070\000\140\002\
\\071\000\140\002\073\000\140\002\074\000\140\002\076\000\140\002\
\\077\000\140\002\078\000\140\002\079\000\140\002\080\000\140\002\
\\081\000\140\002\082\000\140\002\084\000\140\002\085\000\140\002\
\\086\000\140\002\087\000\140\002\088\000\140\002\089\000\140\002\
\\090\000\140\002\093\000\140\002\095\000\140\002\098\000\140\002\
\\101\000\140\002\103\000\140\002\000\000\
\\001\000\002\000\141\002\005\000\141\002\006\000\141\002\009\000\141\002\
\\011\000\141\002\012\000\141\002\035\000\141\002\049\000\141\002\
\\063\000\141\002\064\000\141\002\065\000\141\002\066\000\141\002\
\\067\000\141\002\068\000\141\002\069\000\141\002\070\000\141\002\
\\071\000\141\002\073\000\141\002\074\000\141\002\076\000\141\002\
\\077\000\141\002\078\000\141\002\079\000\141\002\080\000\141\002\
\\081\000\141\002\082\000\141\002\084\000\141\002\085\000\141\002\
\\086\000\141\002\087\000\141\002\088\000\141\002\089\000\141\002\
\\090\000\141\002\093\000\141\002\095\000\141\002\098\000\141\002\
\\101\000\141\002\103\000\141\002\000\000\
\\001\000\002\000\142\002\005\000\142\002\006\000\142\002\009\000\142\002\
\\011\000\142\002\012\000\142\002\035\000\142\002\049\000\142\002\
\\063\000\142\002\064\000\142\002\065\000\142\002\066\000\142\002\
\\067\000\142\002\068\000\142\002\069\000\142\002\070\000\142\002\
\\071\000\142\002\073\000\142\002\074\000\142\002\076\000\142\002\
\\077\000\142\002\078\000\142\002\079\000\142\002\080\000\142\002\
\\081\000\142\002\082\000\142\002\084\000\142\002\085\000\142\002\
\\086\000\142\002\087\000\142\002\088\000\142\002\089\000\142\002\
\\090\000\142\002\093\000\142\002\095\000\142\002\098\000\142\002\
\\101\000\142\002\103\000\142\002\000\000\
\\001\000\002\000\143\002\005\000\143\002\006\000\143\002\009\000\143\002\
\\011\000\143\002\012\000\143\002\035\000\143\002\049\000\143\002\
\\063\000\143\002\064\000\143\002\065\000\143\002\066\000\143\002\
\\067\000\143\002\068\000\143\002\069\000\143\002\070\000\143\002\
\\071\000\143\002\073\000\143\002\074\000\143\002\076\000\143\002\
\\077\000\143\002\078\000\143\002\079\000\143\002\080\000\143\002\
\\081\000\143\002\082\000\143\002\084\000\143\002\085\000\143\002\
\\086\000\143\002\087\000\143\002\088\000\143\002\089\000\143\002\
\\090\000\143\002\093\000\143\002\095\000\143\002\098\000\143\002\
\\101\000\143\002\103\000\143\002\000\000\
\\001\000\002\000\144\002\005\000\144\002\006\000\144\002\009\000\144\002\
\\011\000\144\002\012\000\144\002\035\000\144\002\049\000\144\002\
\\063\000\144\002\064\000\144\002\065\000\144\002\066\000\144\002\
\\067\000\144\002\068\000\144\002\069\000\144\002\070\000\144\002\
\\071\000\144\002\073\000\144\002\074\000\144\002\076\000\144\002\
\\077\000\144\002\078\000\144\002\079\000\144\002\080\000\144\002\
\\081\000\144\002\082\000\144\002\084\000\144\002\085\000\144\002\
\\086\000\144\002\087\000\144\002\088\000\144\002\089\000\144\002\
\\090\000\144\002\093\000\144\002\095\000\144\002\098\000\144\002\
\\101\000\144\002\103\000\144\002\000\000\
\\001\000\002\000\145\002\005\000\145\002\006\000\145\002\007\000\140\000\
\\009\000\145\002\011\000\145\002\012\000\145\002\035\000\145\002\
\\049\000\145\002\063\000\145\002\064\000\145\002\065\000\145\002\
\\066\000\145\002\067\000\145\002\068\000\145\002\069\000\145\002\
\\070\000\145\002\071\000\145\002\073\000\145\002\074\000\145\002\
\\076\000\145\002\077\000\145\002\078\000\145\002\079\000\145\002\
\\080\000\145\002\081\000\145\002\082\000\145\002\084\000\145\002\
\\085\000\145\002\086\000\145\002\087\000\145\002\088\000\145\002\
\\089\000\145\002\090\000\145\002\093\000\145\002\095\000\145\002\
\\098\000\145\002\101\000\145\002\103\000\145\002\000\000\
\\001\000\002\000\166\002\005\000\166\002\007\000\166\002\018\000\166\002\
\\020\000\166\002\021\000\166\002\022\000\166\002\048\000\166\002\
\\050\000\166\002\073\000\166\002\075\000\166\002\099\000\166\002\000\000\
\\001\000\002\000\173\002\005\000\173\002\018\000\173\002\020\000\173\002\
\\021\000\173\002\022\000\173\002\048\000\173\002\050\000\173\002\
\\073\000\173\002\075\000\173\002\099\000\173\002\000\000\
\\001\000\002\000\174\002\005\000\174\002\018\000\174\002\020\000\174\002\
\\021\000\174\002\022\000\174\002\048\000\174\002\050\000\174\002\
\\073\000\174\002\075\000\174\002\099\000\174\002\000\000\
\\001\000\002\000\175\002\005\000\175\002\018\000\175\002\020\000\175\002\
\\021\000\175\002\022\000\175\002\048\000\175\002\050\000\175\002\
\\073\000\175\002\075\000\175\002\099\000\175\002\000\000\
\\001\000\002\000\176\002\005\000\176\002\018\000\176\002\020\000\176\002\
\\021\000\176\002\022\000\176\002\048\000\176\002\050\000\176\002\
\\073\000\176\002\075\000\176\002\099\000\176\002\000\000\
\\001\000\002\000\177\002\005\000\177\002\018\000\177\002\020\000\177\002\
\\021\000\177\002\022\000\177\002\048\000\177\002\050\000\177\002\
\\073\000\177\002\075\000\177\002\099\000\177\002\000\000\
\\001\000\002\000\178\002\005\000\178\002\018\000\178\002\020\000\178\002\
\\021\000\178\002\022\000\178\002\048\000\178\002\050\000\178\002\
\\073\000\178\002\075\000\178\002\099\000\178\002\000\000\
\\001\000\002\000\179\002\005\000\179\002\018\000\179\002\020\000\179\002\
\\021\000\179\002\022\000\179\002\048\000\179\002\050\000\179\002\
\\073\000\179\002\075\000\179\002\099\000\179\002\000\000\
\\001\000\002\000\180\002\005\000\180\002\018\000\180\002\020\000\180\002\
\\021\000\180\002\022\000\180\002\048\000\180\002\050\000\180\002\
\\073\000\180\002\075\000\180\002\099\000\180\002\000\000\
\\001\000\002\000\181\002\005\000\181\002\018\000\181\002\020\000\181\002\
\\021\000\181\002\022\000\181\002\048\000\181\002\050\000\181\002\
\\073\000\181\002\075\000\181\002\099\000\181\002\000\000\
\\001\000\002\000\182\002\005\000\182\002\018\000\182\002\020\000\182\002\
\\021\000\182\002\022\000\182\002\048\000\182\002\050\000\182\002\
\\073\000\182\002\075\000\182\002\099\000\182\002\000\000\
\\001\000\002\000\183\002\005\000\183\002\018\000\183\002\020\000\183\002\
\\021\000\183\002\022\000\183\002\048\000\183\002\050\000\183\002\
\\073\000\183\002\075\000\183\002\099\000\183\002\000\000\
\\001\000\002\000\185\002\005\000\185\002\007\000\185\002\008\000\185\002\
\\012\000\185\002\018\000\185\002\020\000\185\002\021\000\185\002\
\\022\000\185\002\035\000\185\002\036\000\185\002\037\000\185\002\
\\038\000\185\002\039\000\185\002\040\000\185\002\041\000\185\002\
\\042\000\185\002\043\000\185\002\044\000\185\002\045\000\185\002\
\\046\000\185\002\047\000\185\002\048\000\185\002\049\000\185\002\
\\050\000\185\002\063\000\185\002\064\000\185\002\065\000\185\002\
\\066\000\185\002\067\000\185\002\068\000\185\002\069\000\185\002\
\\070\000\185\002\071\000\185\002\073\000\185\002\074\000\185\002\
\\075\000\185\002\076\000\185\002\077\000\185\002\078\000\185\002\
\\079\000\185\002\080\000\185\002\081\000\185\002\082\000\185\002\
\\084\000\185\002\085\000\185\002\086\000\185\002\087\000\185\002\
\\088\000\185\002\089\000\185\002\090\000\185\002\091\000\185\002\
\\092\000\185\002\093\000\185\002\095\000\185\002\096\000\185\002\
\\097\000\185\002\098\000\185\002\099\000\185\002\101\000\185\002\
\\102\000\185\002\103\000\185\002\000\000\
\\001\000\002\000\186\002\005\000\186\002\007\000\186\002\008\000\186\002\
\\012\000\186\002\018\000\186\002\020\000\186\002\021\000\186\002\
\\022\000\186\002\035\000\186\002\036\000\186\002\037\000\186\002\
\\038\000\186\002\039\000\186\002\040\000\186\002\041\000\186\002\
\\042\000\186\002\043\000\186\002\044\000\186\002\045\000\186\002\
\\046\000\186\002\047\000\186\002\048\000\186\002\049\000\186\002\
\\050\000\186\002\063\000\186\002\064\000\186\002\065\000\186\002\
\\066\000\186\002\067\000\186\002\068\000\186\002\069\000\186\002\
\\070\000\186\002\071\000\186\002\073\000\186\002\074\000\186\002\
\\075\000\186\002\076\000\186\002\077\000\186\002\078\000\186\002\
\\079\000\186\002\080\000\186\002\081\000\186\002\082\000\186\002\
\\084\000\186\002\085\000\186\002\086\000\186\002\087\000\186\002\
\\088\000\186\002\089\000\186\002\090\000\186\002\091\000\186\002\
\\092\000\186\002\093\000\186\002\095\000\186\002\096\000\186\002\
\\097\000\186\002\098\000\186\002\099\000\186\002\101\000\186\002\
\\102\000\186\002\103\000\186\002\000\000\
\\001\000\002\000\187\002\005\000\187\002\007\000\187\002\008\000\187\002\
\\012\000\187\002\018\000\187\002\020\000\187\002\021\000\187\002\
\\022\000\187\002\035\000\187\002\036\000\187\002\037\000\187\002\
\\038\000\187\002\039\000\187\002\040\000\187\002\041\000\187\002\
\\042\000\187\002\043\000\187\002\044\000\187\002\045\000\187\002\
\\046\000\187\002\047\000\187\002\048\000\187\002\049\000\187\002\
\\050\000\187\002\063\000\187\002\064\000\187\002\065\000\187\002\
\\066\000\187\002\067\000\187\002\068\000\187\002\069\000\187\002\
\\070\000\187\002\071\000\187\002\073\000\187\002\074\000\187\002\
\\075\000\187\002\076\000\187\002\077\000\187\002\078\000\187\002\
\\079\000\187\002\080\000\187\002\081\000\187\002\082\000\187\002\
\\084\000\187\002\085\000\187\002\086\000\187\002\087\000\187\002\
\\088\000\187\002\089\000\187\002\090\000\187\002\091\000\187\002\
\\092\000\187\002\093\000\187\002\095\000\187\002\096\000\187\002\
\\097\000\187\002\098\000\187\002\099\000\187\002\101\000\187\002\
\\102\000\187\002\103\000\187\002\000\000\
\\001\000\002\000\188\002\005\000\188\002\007\000\188\002\008\000\188\002\
\\012\000\188\002\018\000\188\002\020\000\188\002\021\000\188\002\
\\022\000\188\002\035\000\188\002\036\000\188\002\037\000\188\002\
\\038\000\188\002\039\000\188\002\040\000\188\002\041\000\188\002\
\\042\000\188\002\043\000\188\002\044\000\188\002\045\000\188\002\
\\046\000\188\002\047\000\188\002\048\000\188\002\049\000\188\002\
\\050\000\188\002\063\000\188\002\064\000\188\002\065\000\188\002\
\\066\000\188\002\067\000\188\002\068\000\188\002\069\000\188\002\
\\070\000\188\002\071\000\188\002\073\000\188\002\074\000\188\002\
\\075\000\188\002\076\000\188\002\077\000\188\002\078\000\188\002\
\\079\000\188\002\080\000\188\002\081\000\188\002\082\000\188\002\
\\084\000\188\002\085\000\188\002\086\000\188\002\087\000\188\002\
\\088\000\188\002\089\000\188\002\090\000\188\002\091\000\188\002\
\\092\000\188\002\093\000\188\002\095\000\188\002\096\000\188\002\
\\097\000\188\002\098\000\188\002\099\000\188\002\101\000\188\002\
\\102\000\188\002\103\000\188\002\000\000\
\\001\000\002\000\189\002\005\000\189\002\007\000\189\002\008\000\189\002\
\\012\000\189\002\018\000\189\002\020\000\189\002\021\000\189\002\
\\022\000\189\002\035\000\189\002\036\000\189\002\037\000\189\002\
\\038\000\189\002\039\000\189\002\040\000\189\002\041\000\189\002\
\\042\000\189\002\043\000\189\002\044\000\189\002\045\000\189\002\
\\046\000\189\002\047\000\189\002\048\000\189\002\049\000\189\002\
\\050\000\189\002\063\000\189\002\064\000\189\002\065\000\189\002\
\\066\000\189\002\067\000\189\002\068\000\189\002\069\000\189\002\
\\070\000\189\002\071\000\189\002\073\000\189\002\074\000\189\002\
\\075\000\189\002\076\000\189\002\077\000\189\002\078\000\189\002\
\\079\000\189\002\080\000\189\002\081\000\189\002\082\000\189\002\
\\084\000\189\002\085\000\189\002\086\000\189\002\087\000\189\002\
\\088\000\189\002\089\000\189\002\090\000\189\002\091\000\189\002\
\\092\000\189\002\093\000\189\002\095\000\189\002\096\000\189\002\
\\097\000\189\002\098\000\189\002\099\000\189\002\101\000\189\002\
\\102\000\189\002\103\000\189\002\000\000\
\\001\000\002\000\190\002\005\000\190\002\007\000\190\002\008\000\190\002\
\\012\000\190\002\018\000\190\002\020\000\190\002\021\000\190\002\
\\022\000\190\002\035\000\190\002\036\000\190\002\037\000\190\002\
\\038\000\190\002\039\000\190\002\040\000\190\002\041\000\190\002\
\\042\000\190\002\043\000\190\002\044\000\190\002\045\000\190\002\
\\046\000\190\002\047\000\190\002\048\000\190\002\049\000\190\002\
\\050\000\190\002\063\000\190\002\064\000\190\002\065\000\190\002\
\\066\000\190\002\067\000\190\002\068\000\190\002\069\000\190\002\
\\070\000\190\002\071\000\190\002\073\000\190\002\074\000\190\002\
\\075\000\190\002\076\000\190\002\077\000\190\002\078\000\190\002\
\\079\000\190\002\080\000\190\002\081\000\190\002\082\000\190\002\
\\084\000\190\002\085\000\190\002\086\000\190\002\087\000\190\002\
\\088\000\190\002\089\000\190\002\090\000\190\002\091\000\190\002\
\\092\000\190\002\093\000\190\002\095\000\190\002\096\000\190\002\
\\097\000\190\002\098\000\190\002\099\000\190\002\101\000\190\002\
\\102\000\190\002\103\000\190\002\000\000\
\\001\000\002\000\191\002\005\000\191\002\007\000\191\002\008\000\191\002\
\\012\000\191\002\018\000\191\002\020\000\191\002\021\000\191\002\
\\022\000\191\002\035\000\191\002\036\000\191\002\037\000\191\002\
\\038\000\191\002\039\000\191\002\040\000\191\002\041\000\191\002\
\\042\000\191\002\043\000\191\002\044\000\191\002\045\000\191\002\
\\046\000\191\002\047\000\191\002\048\000\191\002\049\000\191\002\
\\050\000\191\002\063\000\191\002\064\000\191\002\065\000\191\002\
\\066\000\191\002\067\000\191\002\068\000\191\002\069\000\191\002\
\\070\000\191\002\071\000\191\002\073\000\191\002\074\000\191\002\
\\075\000\191\002\076\000\191\002\077\000\191\002\078\000\191\002\
\\079\000\191\002\080\000\191\002\081\000\191\002\082\000\191\002\
\\084\000\191\002\085\000\191\002\086\000\191\002\087\000\191\002\
\\088\000\191\002\089\000\191\002\090\000\191\002\091\000\191\002\
\\092\000\191\002\093\000\191\002\095\000\191\002\096\000\191\002\
\\097\000\191\002\098\000\191\002\099\000\191\002\101\000\191\002\
\\102\000\191\002\103\000\191\002\000\000\
\\001\000\002\000\192\002\005\000\192\002\007\000\192\002\008\000\192\002\
\\012\000\192\002\018\000\192\002\020\000\192\002\021\000\192\002\
\\022\000\192\002\035\000\192\002\036\000\192\002\037\000\192\002\
\\038\000\192\002\039\000\192\002\040\000\192\002\041\000\192\002\
\\042\000\192\002\043\000\192\002\044\000\192\002\045\000\192\002\
\\046\000\192\002\047\000\192\002\048\000\192\002\049\000\192\002\
\\050\000\192\002\063\000\192\002\064\000\192\002\065\000\192\002\
\\066\000\192\002\067\000\192\002\068\000\192\002\069\000\192\002\
\\070\000\192\002\071\000\192\002\073\000\192\002\074\000\192\002\
\\075\000\192\002\076\000\192\002\077\000\192\002\078\000\192\002\
\\079\000\192\002\080\000\192\002\081\000\192\002\082\000\192\002\
\\084\000\192\002\085\000\192\002\086\000\192\002\087\000\192\002\
\\088\000\192\002\089\000\192\002\090\000\192\002\091\000\192\002\
\\092\000\192\002\093\000\192\002\095\000\192\002\096\000\192\002\
\\097\000\192\002\098\000\192\002\099\000\192\002\101\000\192\002\
\\102\000\192\002\103\000\192\002\000\000\
\\001\000\002\000\193\002\005\000\193\002\007\000\193\002\008\000\193\002\
\\012\000\193\002\018\000\193\002\020\000\193\002\021\000\193\002\
\\022\000\193\002\035\000\193\002\036\000\193\002\037\000\193\002\
\\038\000\193\002\039\000\193\002\040\000\193\002\041\000\193\002\
\\042\000\193\002\043\000\193\002\044\000\193\002\045\000\193\002\
\\046\000\193\002\047\000\193\002\048\000\193\002\049\000\193\002\
\\050\000\193\002\063\000\193\002\064\000\193\002\065\000\193\002\
\\066\000\193\002\067\000\193\002\068\000\193\002\069\000\193\002\
\\070\000\193\002\071\000\193\002\073\000\193\002\074\000\193\002\
\\075\000\193\002\076\000\193\002\077\000\193\002\078\000\193\002\
\\079\000\193\002\080\000\193\002\081\000\193\002\082\000\193\002\
\\084\000\193\002\085\000\193\002\086\000\193\002\087\000\193\002\
\\088\000\193\002\089\000\193\002\090\000\193\002\091\000\193\002\
\\092\000\193\002\093\000\193\002\095\000\193\002\096\000\193\002\
\\097\000\193\002\098\000\193\002\099\000\193\002\101\000\193\002\
\\102\000\193\002\103\000\193\002\000\000\
\\001\000\002\000\194\002\005\000\194\002\007\000\194\002\008\000\194\002\
\\012\000\194\002\018\000\194\002\020\000\194\002\021\000\194\002\
\\022\000\194\002\035\000\194\002\036\000\194\002\037\000\194\002\
\\038\000\194\002\039\000\194\002\040\000\194\002\041\000\194\002\
\\042\000\194\002\043\000\194\002\044\000\194\002\045\000\194\002\
\\046\000\194\002\047\000\194\002\048\000\194\002\049\000\194\002\
\\050\000\194\002\063\000\194\002\064\000\194\002\065\000\194\002\
\\066\000\194\002\067\000\194\002\068\000\194\002\069\000\194\002\
\\070\000\194\002\071\000\194\002\073\000\194\002\074\000\194\002\
\\075\000\194\002\076\000\194\002\077\000\194\002\078\000\194\002\
\\079\000\194\002\080\000\194\002\081\000\194\002\082\000\194\002\
\\084\000\194\002\085\000\194\002\086\000\194\002\087\000\194\002\
\\088\000\194\002\089\000\194\002\090\000\194\002\091\000\194\002\
\\092\000\194\002\093\000\194\002\095\000\194\002\096\000\194\002\
\\097\000\194\002\098\000\194\002\099\000\194\002\101\000\194\002\
\\102\000\194\002\103\000\194\002\000\000\
\\001\000\002\000\195\002\005\000\195\002\007\000\195\002\008\000\195\002\
\\012\000\195\002\018\000\195\002\020\000\195\002\021\000\195\002\
\\022\000\195\002\035\000\195\002\036\000\195\002\037\000\222\001\
\\038\000\195\002\039\000\195\002\040\000\195\002\041\000\195\002\
\\042\000\195\002\043\000\195\002\044\000\195\002\045\000\195\002\
\\046\000\195\002\047\000\195\002\048\000\195\002\049\000\195\002\
\\050\000\195\002\063\000\195\002\064\000\195\002\065\000\195\002\
\\066\000\195\002\067\000\195\002\068\000\195\002\069\000\195\002\
\\070\000\195\002\071\000\195\002\073\000\195\002\074\000\195\002\
\\075\000\195\002\076\000\195\002\077\000\195\002\078\000\195\002\
\\079\000\195\002\080\000\195\002\081\000\195\002\082\000\195\002\
\\084\000\195\002\085\000\195\002\086\000\195\002\087\000\195\002\
\\088\000\195\002\089\000\195\002\090\000\195\002\091\000\195\002\
\\092\000\195\002\093\000\195\002\095\000\195\002\096\000\195\002\
\\097\000\195\002\098\000\195\002\099\000\195\002\101\000\195\002\
\\102\000\195\002\103\000\195\002\000\000\
\\001\000\002\000\196\002\005\000\196\002\007\000\196\002\008\000\196\002\
\\012\000\196\002\018\000\196\002\020\000\196\002\021\000\196\002\
\\022\000\196\002\035\000\196\002\036\000\196\002\037\000\196\002\
\\038\000\196\002\039\000\196\002\040\000\196\002\041\000\196\002\
\\042\000\196\002\043\000\196\002\044\000\196\002\045\000\196\002\
\\046\000\196\002\047\000\196\002\048\000\196\002\049\000\196\002\
\\050\000\196\002\063\000\196\002\064\000\196\002\065\000\196\002\
\\066\000\196\002\067\000\196\002\068\000\196\002\069\000\196\002\
\\070\000\196\002\071\000\196\002\073\000\196\002\074\000\196\002\
\\075\000\196\002\076\000\196\002\077\000\196\002\078\000\196\002\
\\079\000\196\002\080\000\196\002\081\000\196\002\082\000\196\002\
\\084\000\196\002\085\000\196\002\086\000\196\002\087\000\196\002\
\\088\000\196\002\089\000\196\002\090\000\196\002\091\000\196\002\
\\092\000\196\002\093\000\196\002\095\000\196\002\096\000\196\002\
\\097\000\196\002\098\000\196\002\099\000\196\002\101\000\196\002\
\\102\000\196\002\103\000\196\002\000\000\
\\001\000\002\000\197\002\005\000\197\002\007\000\197\002\008\000\197\002\
\\012\000\197\002\018\000\197\002\020\000\197\002\021\000\197\002\
\\022\000\197\002\035\000\197\002\036\000\197\002\037\000\197\002\
\\038\000\197\002\039\000\197\002\040\000\197\002\041\000\197\002\
\\042\000\197\002\043\000\197\002\044\000\197\002\045\000\197\002\
\\046\000\197\002\047\000\197\002\048\000\197\002\049\000\197\002\
\\050\000\197\002\063\000\197\002\064\000\197\002\065\000\197\002\
\\066\000\197\002\067\000\197\002\068\000\197\002\069\000\197\002\
\\070\000\197\002\071\000\197\002\073\000\197\002\074\000\197\002\
\\075\000\197\002\076\000\197\002\077\000\197\002\078\000\197\002\
\\079\000\197\002\080\000\197\002\081\000\197\002\082\000\197\002\
\\084\000\197\002\085\000\197\002\086\000\197\002\087\000\197\002\
\\088\000\197\002\089\000\197\002\090\000\197\002\091\000\197\002\
\\092\000\197\002\093\000\197\002\095\000\197\002\096\000\197\002\
\\097\000\197\002\098\000\197\002\099\000\197\002\101\000\197\002\
\\102\000\197\002\103\000\197\002\000\000\
\\001\000\002\000\198\002\005\000\198\002\007\000\198\002\008\000\198\002\
\\012\000\198\002\018\000\198\002\020\000\198\002\021\000\198\002\
\\022\000\198\002\035\000\198\002\036\000\198\002\037\000\198\002\
\\038\000\198\002\039\000\198\002\040\000\198\002\041\000\198\002\
\\042\000\198\002\043\000\198\002\044\000\198\002\045\000\198\002\
\\046\000\198\002\047\000\198\002\048\000\198\002\049\000\198\002\
\\050\000\198\002\063\000\198\002\064\000\198\002\065\000\198\002\
\\066\000\198\002\067\000\198\002\068\000\198\002\069\000\198\002\
\\070\000\198\002\071\000\198\002\073\000\198\002\074\000\198\002\
\\075\000\198\002\076\000\198\002\077\000\198\002\078\000\198\002\
\\079\000\198\002\080\000\198\002\081\000\198\002\082\000\198\002\
\\084\000\198\002\085\000\198\002\086\000\198\002\087\000\198\002\
\\088\000\198\002\089\000\198\002\090\000\198\002\091\000\198\002\
\\092\000\198\002\093\000\198\002\095\000\198\002\096\000\198\002\
\\097\000\198\002\098\000\198\002\099\000\198\002\101\000\198\002\
\\102\000\198\002\103\000\198\002\000\000\
\\001\000\002\000\199\002\005\000\199\002\007\000\199\002\008\000\199\002\
\\012\000\199\002\018\000\199\002\020\000\199\002\021\000\199\002\
\\022\000\199\002\035\000\199\002\036\000\199\002\037\000\199\002\
\\038\000\199\002\039\000\199\002\040\000\199\002\041\000\199\002\
\\042\000\199\002\043\000\199\002\044\000\199\002\045\000\199\002\
\\046\000\199\002\047\000\199\002\048\000\199\002\049\000\199\002\
\\050\000\199\002\063\000\199\002\064\000\199\002\065\000\199\002\
\\066\000\199\002\067\000\199\002\068\000\199\002\069\000\199\002\
\\070\000\199\002\071\000\199\002\073\000\199\002\074\000\199\002\
\\075\000\199\002\076\000\199\002\077\000\199\002\078\000\199\002\
\\079\000\199\002\080\000\199\002\081\000\199\002\082\000\199\002\
\\084\000\199\002\085\000\199\002\086\000\199\002\087\000\199\002\
\\088\000\199\002\089\000\199\002\090\000\199\002\091\000\199\002\
\\092\000\199\002\093\000\199\002\095\000\199\002\096\000\199\002\
\\097\000\199\002\098\000\199\002\099\000\199\002\101\000\199\002\
\\102\000\199\002\103\000\199\002\000\000\
\\001\000\002\000\200\002\005\000\200\002\007\000\200\002\008\000\200\002\
\\012\000\200\002\018\000\200\002\020\000\200\002\021\000\200\002\
\\022\000\200\002\035\000\200\002\036\000\200\002\037\000\200\002\
\\038\000\200\002\039\000\200\002\040\000\200\002\041\000\200\002\
\\042\000\200\002\043\000\200\002\044\000\200\002\045\000\200\002\
\\046\000\200\002\047\000\200\002\048\000\200\002\049\000\200\002\
\\050\000\200\002\063\000\200\002\064\000\200\002\065\000\200\002\
\\066\000\200\002\067\000\200\002\068\000\200\002\069\000\200\002\
\\070\000\200\002\071\000\200\002\073\000\200\002\074\000\200\002\
\\075\000\200\002\076\000\200\002\077\000\200\002\078\000\200\002\
\\079\000\200\002\080\000\200\002\081\000\200\002\082\000\200\002\
\\084\000\200\002\085\000\200\002\086\000\200\002\087\000\200\002\
\\088\000\200\002\089\000\200\002\090\000\200\002\091\000\200\002\
\\092\000\200\002\093\000\200\002\095\000\200\002\096\000\200\002\
\\097\000\200\002\098\000\200\002\099\000\200\002\101\000\200\002\
\\102\000\200\002\103\000\200\002\000\000\
\\001\000\002\000\201\002\005\000\201\002\007\000\201\002\008\000\201\002\
\\012\000\201\002\018\000\201\002\020\000\201\002\021\000\201\002\
\\022\000\201\002\035\000\201\002\036\000\201\002\037\000\201\002\
\\038\000\201\002\039\000\201\002\040\000\201\002\041\000\201\002\
\\042\000\201\002\043\000\201\002\044\000\201\002\045\000\201\002\
\\046\000\201\002\047\000\201\002\048\000\201\002\049\000\201\002\
\\050\000\201\002\063\000\201\002\064\000\201\002\065\000\201\002\
\\066\000\201\002\067\000\201\002\068\000\201\002\069\000\201\002\
\\070\000\201\002\071\000\201\002\073\000\201\002\074\000\201\002\
\\075\000\201\002\076\000\201\002\077\000\201\002\078\000\201\002\
\\079\000\201\002\080\000\201\002\081\000\201\002\082\000\201\002\
\\084\000\201\002\085\000\201\002\086\000\201\002\087\000\201\002\
\\088\000\201\002\089\000\201\002\090\000\201\002\091\000\201\002\
\\092\000\201\002\093\000\201\002\095\000\201\002\096\000\201\002\
\\097\000\201\002\098\000\201\002\099\000\201\002\101\000\201\002\
\\102\000\201\002\103\000\201\002\000\000\
\\001\000\002\000\202\002\005\000\202\002\007\000\202\002\008\000\202\002\
\\012\000\202\002\018\000\202\002\020\000\202\002\021\000\202\002\
\\022\000\202\002\035\000\202\002\036\000\202\002\037\000\202\002\
\\038\000\202\002\039\000\202\002\040\000\202\002\041\000\202\002\
\\042\000\202\002\043\000\202\002\044\000\202\002\045\000\202\002\
\\046\000\202\002\047\000\202\002\048\000\202\002\049\000\202\002\
\\050\000\202\002\063\000\202\002\064\000\202\002\065\000\202\002\
\\066\000\202\002\067\000\202\002\068\000\202\002\069\000\202\002\
\\070\000\202\002\071\000\202\002\073\000\202\002\074\000\202\002\
\\075\000\202\002\076\000\202\002\077\000\202\002\078\000\202\002\
\\079\000\202\002\080\000\202\002\081\000\202\002\082\000\202\002\
\\084\000\202\002\085\000\202\002\086\000\202\002\087\000\202\002\
\\088\000\202\002\089\000\202\002\090\000\202\002\091\000\202\002\
\\092\000\202\002\093\000\202\002\095\000\202\002\096\000\202\002\
\\097\000\202\002\098\000\202\002\099\000\202\002\101\000\202\002\
\\102\000\202\002\103\000\202\002\000\000\
\\001\000\002\000\203\002\005\000\203\002\007\000\203\002\008\000\203\002\
\\012\000\203\002\018\000\203\002\020\000\203\002\021\000\203\002\
\\022\000\203\002\035\000\203\002\036\000\203\002\037\000\203\002\
\\038\000\203\002\039\000\203\002\040\000\203\002\041\000\203\002\
\\042\000\203\002\043\000\203\002\044\000\203\002\045\000\203\002\
\\046\000\203\002\047\000\203\002\048\000\203\002\049\000\203\002\
\\050\000\203\002\063\000\203\002\064\000\203\002\065\000\203\002\
\\066\000\203\002\067\000\203\002\068\000\203\002\069\000\203\002\
\\070\000\203\002\071\000\203\002\073\000\203\002\074\000\203\002\
\\075\000\203\002\076\000\203\002\077\000\203\002\078\000\203\002\
\\079\000\203\002\080\000\203\002\081\000\203\002\082\000\203\002\
\\084\000\203\002\085\000\203\002\086\000\203\002\087\000\203\002\
\\088\000\203\002\089\000\203\002\090\000\203\002\091\000\203\002\
\\092\000\203\002\093\000\203\002\095\000\203\002\096\000\203\002\
\\097\000\203\002\098\000\203\002\099\000\203\002\101\000\203\002\
\\102\000\203\002\103\000\203\002\000\000\
\\001\000\002\000\204\002\005\000\204\002\007\000\204\002\008\000\204\002\
\\012\000\204\002\018\000\204\002\020\000\204\002\021\000\204\002\
\\022\000\204\002\035\000\204\002\036\000\204\002\037\000\204\002\
\\038\000\204\002\039\000\204\002\040\000\204\002\041\000\204\002\
\\042\000\204\002\043\000\204\002\044\000\204\002\045\000\204\002\
\\046\000\204\002\047\000\204\002\048\000\204\002\049\000\204\002\
\\050\000\204\002\063\000\204\002\064\000\204\002\065\000\204\002\
\\066\000\204\002\067\000\204\002\068\000\204\002\069\000\204\002\
\\070\000\204\002\071\000\204\002\073\000\204\002\074\000\204\002\
\\075\000\204\002\076\000\204\002\077\000\204\002\078\000\204\002\
\\079\000\204\002\080\000\204\002\081\000\204\002\082\000\204\002\
\\084\000\204\002\085\000\204\002\086\000\204\002\087\000\204\002\
\\088\000\204\002\089\000\204\002\090\000\204\002\091\000\204\002\
\\092\000\204\002\093\000\204\002\095\000\204\002\096\000\204\002\
\\097\000\204\002\098\000\204\002\099\000\204\002\101\000\204\002\
\\102\000\204\002\103\000\204\002\000\000\
\\001\000\002\000\205\002\005\000\205\002\007\000\205\002\008\000\205\002\
\\012\000\205\002\018\000\205\002\020\000\205\002\021\000\205\002\
\\022\000\205\002\035\000\205\002\036\000\205\002\037\000\205\002\
\\038\000\205\002\039\000\205\002\040\000\205\002\041\000\205\002\
\\042\000\205\002\043\000\205\002\044\000\205\002\045\000\205\002\
\\046\000\205\002\047\000\205\002\048\000\205\002\049\000\205\002\
\\050\000\205\002\063\000\205\002\064\000\205\002\065\000\205\002\
\\066\000\205\002\067\000\205\002\068\000\205\002\069\000\205\002\
\\070\000\205\002\071\000\205\002\073\000\205\002\074\000\205\002\
\\075\000\205\002\076\000\205\002\077\000\205\002\078\000\205\002\
\\079\000\205\002\080\000\205\002\081\000\205\002\082\000\205\002\
\\084\000\205\002\085\000\205\002\086\000\205\002\087\000\205\002\
\\088\000\205\002\089\000\205\002\090\000\205\002\091\000\205\002\
\\092\000\205\002\093\000\205\002\095\000\205\002\096\000\205\002\
\\097\000\205\002\098\000\205\002\099\000\205\002\101\000\205\002\
\\102\000\205\002\103\000\205\002\000\000\
\\001\000\002\000\206\002\005\000\206\002\007\000\206\002\008\000\206\002\
\\012\000\206\002\018\000\206\002\020\000\206\002\021\000\206\002\
\\022\000\206\002\035\000\206\002\036\000\206\002\037\000\206\002\
\\038\000\206\002\039\000\206\002\040\000\206\002\041\000\206\002\
\\042\000\206\002\043\000\206\002\044\000\206\002\045\000\206\002\
\\046\000\206\002\047\000\206\002\048\000\206\002\049\000\206\002\
\\050\000\206\002\063\000\206\002\064\000\206\002\065\000\206\002\
\\066\000\206\002\067\000\206\002\068\000\206\002\069\000\206\002\
\\070\000\206\002\071\000\206\002\073\000\206\002\074\000\206\002\
\\075\000\206\002\076\000\206\002\077\000\206\002\078\000\206\002\
\\079\000\206\002\080\000\206\002\081\000\206\002\082\000\206\002\
\\084\000\206\002\085\000\206\002\086\000\206\002\087\000\206\002\
\\088\000\206\002\089\000\206\002\090\000\206\002\091\000\206\002\
\\092\000\206\002\093\000\206\002\095\000\206\002\096\000\206\002\
\\097\000\206\002\098\000\206\002\099\000\206\002\101\000\206\002\
\\102\000\206\002\103\000\206\002\000\000\
\\001\000\002\000\224\002\005\000\224\002\007\000\224\002\012\000\224\002\
\\018\000\224\002\020\000\224\002\021\000\224\002\022\000\224\002\
\\036\000\224\002\038\000\224\002\039\000\224\002\040\000\224\002\
\\041\000\224\002\042\000\224\002\043\000\224\002\044\000\224\002\
\\045\000\224\002\048\000\224\002\050\000\224\002\073\000\224\002\
\\075\000\224\002\091\000\224\002\092\000\224\002\096\000\224\002\
\\099\000\224\002\102\000\224\002\000\000\
\\001\000\002\000\225\002\005\000\225\002\007\000\225\002\012\000\225\002\
\\018\000\225\002\020\000\225\002\021\000\225\002\022\000\225\002\
\\036\000\225\002\038\000\225\002\039\000\225\002\040\000\225\002\
\\041\000\225\002\042\000\225\002\043\000\225\002\044\000\225\002\
\\045\000\225\002\048\000\225\002\050\000\225\002\073\000\225\002\
\\075\000\225\002\083\000\037\001\091\000\225\002\092\000\225\002\
\\096\000\225\002\099\000\225\002\102\000\225\002\000\000\
\\001\000\002\000\226\002\005\000\226\002\007\000\226\002\012\000\226\002\
\\018\000\226\002\020\000\226\002\021\000\226\002\022\000\226\002\
\\036\000\226\002\038\000\226\002\039\000\226\002\040\000\226\002\
\\041\000\226\002\042\000\226\002\043\000\226\002\044\000\226\002\
\\045\000\226\002\048\000\226\002\050\000\226\002\073\000\226\002\
\\075\000\226\002\091\000\226\002\092\000\226\002\096\000\226\002\
\\099\000\226\002\102\000\226\002\000\000\
\\001\000\002\000\230\002\005\000\230\002\007\000\230\002\012\000\230\002\
\\018\000\230\002\020\000\230\002\021\000\230\002\022\000\230\002\
\\036\000\230\002\038\000\230\002\039\000\230\002\040\000\230\002\
\\041\000\230\002\042\000\230\002\043\000\230\002\044\000\230\002\
\\045\000\230\002\046\000\215\001\047\000\214\001\048\000\230\002\
\\050\000\230\002\073\000\230\002\075\000\230\002\091\000\230\002\
\\092\000\230\002\096\000\230\002\099\000\230\002\102\000\230\002\000\000\
\\001\000\002\000\231\002\005\000\231\002\007\000\231\002\012\000\231\002\
\\018\000\231\002\020\000\231\002\021\000\231\002\022\000\231\002\
\\036\000\231\002\038\000\231\002\039\000\231\002\040\000\231\002\
\\041\000\231\002\042\000\231\002\043\000\231\002\044\000\231\002\
\\045\000\231\002\048\000\231\002\050\000\231\002\073\000\231\002\
\\075\000\231\002\091\000\231\002\092\000\231\002\096\000\231\002\
\\099\000\231\002\102\000\231\002\000\000\
\\001\000\002\000\232\002\005\000\232\002\007\000\232\002\012\000\232\002\
\\018\000\232\002\020\000\232\002\021\000\232\002\022\000\232\002\
\\036\000\232\002\038\000\232\002\039\000\232\002\040\000\232\002\
\\041\000\232\002\042\000\232\002\043\000\232\002\044\000\232\002\
\\045\000\232\002\046\000\232\002\047\000\232\002\048\000\232\002\
\\050\000\232\002\073\000\232\002\075\000\232\002\091\000\232\002\
\\092\000\232\002\096\000\232\002\099\000\232\002\102\000\232\002\000\000\
\\001\000\002\000\233\002\005\000\233\002\007\000\233\002\012\000\233\002\
\\018\000\233\002\020\000\233\002\021\000\233\002\022\000\233\002\
\\036\000\233\002\038\000\233\002\039\000\233\002\040\000\233\002\
\\041\000\233\002\042\000\233\002\043\000\233\002\044\000\233\002\
\\045\000\233\002\046\000\233\002\047\000\233\002\048\000\233\002\
\\050\000\233\002\073\000\233\002\075\000\233\002\091\000\233\002\
\\092\000\233\002\096\000\233\002\099\000\233\002\102\000\233\002\000\000\
\\001\000\002\000\234\002\005\000\234\002\012\000\234\002\018\000\234\002\
\\020\000\234\002\021\000\234\002\022\000\234\002\048\000\234\002\
\\050\000\234\002\073\000\234\002\075\000\234\002\099\000\234\002\000\000\
\\001\000\002\000\235\002\005\000\235\002\012\000\235\002\018\000\235\002\
\\020\000\235\002\021\000\235\002\022\000\235\002\048\000\235\002\
\\050\000\235\002\073\000\235\002\075\000\235\002\099\000\235\002\000\000\
\\001\000\002\000\025\003\003\000\025\003\004\000\025\003\006\000\025\003\
\\008\000\025\003\010\000\025\003\011\000\025\003\012\000\025\003\
\\013\000\025\003\014\000\025\003\017\000\025\003\018\000\025\003\
\\021\000\025\003\051\000\025\003\052\000\025\003\053\000\025\003\
\\054\000\025\003\055\000\025\003\056\000\025\003\057\000\025\003\
\\058\000\025\003\059\000\025\003\060\000\025\003\061\000\025\003\
\\062\000\025\003\091\000\025\003\000\000\
\\001\000\002\000\026\003\003\000\026\003\004\000\026\003\006\000\026\003\
\\008\000\026\003\010\000\026\003\011\000\026\003\012\000\026\003\
\\013\000\026\003\014\000\026\003\017\000\026\003\018\000\026\003\
\\021\000\026\003\051\000\026\003\052\000\026\003\053\000\026\003\
\\054\000\026\003\055\000\026\003\056\000\026\003\057\000\026\003\
\\058\000\026\003\059\000\026\003\060\000\026\003\061\000\026\003\
\\062\000\026\003\091\000\026\003\000\000\
\\001\000\002\000\027\003\003\000\027\003\004\000\027\003\006\000\027\003\
\\008\000\027\003\010\000\027\003\011\000\027\003\012\000\027\003\
\\013\000\027\003\014\000\027\003\017\000\027\003\018\000\027\003\
\\021\000\027\003\051\000\027\003\052\000\027\003\053\000\027\003\
\\054\000\027\003\055\000\027\003\056\000\027\003\057\000\027\003\
\\058\000\027\003\059\000\027\003\060\000\027\003\061\000\027\003\
\\062\000\027\003\091\000\027\003\000\000\
\\001\000\002\000\028\003\003\000\028\003\004\000\028\003\006\000\028\003\
\\008\000\028\003\010\000\028\003\011\000\028\003\012\000\028\003\
\\013\000\028\003\014\000\028\003\017\000\028\003\018\000\028\003\
\\021\000\028\003\051\000\028\003\052\000\028\003\053\000\028\003\
\\054\000\028\003\055\000\028\003\056\000\028\003\057\000\028\003\
\\058\000\028\003\059\000\028\003\060\000\028\003\061\000\028\003\
\\062\000\028\003\091\000\028\003\000\000\
\\001\000\002\000\029\003\003\000\029\003\004\000\029\003\006\000\029\003\
\\008\000\029\003\010\000\029\003\011\000\029\003\012\000\029\003\
\\013\000\029\003\014\000\029\003\015\000\029\003\017\000\029\003\
\\018\000\029\003\021\000\029\003\023\000\029\003\024\000\029\003\
\\025\000\029\003\026\000\029\003\027\000\029\003\028\000\029\003\
\\029\000\029\003\030\000\029\003\031\000\029\003\032\000\029\003\
\\033\000\029\003\034\000\029\003\051\000\029\003\052\000\029\003\
\\053\000\029\003\054\000\029\003\055\000\029\003\056\000\029\003\
\\057\000\029\003\058\000\029\003\059\000\029\003\060\000\029\003\
\\061\000\029\003\062\000\029\003\091\000\029\003\000\000\
\\001\000\002\000\030\003\003\000\030\003\004\000\030\003\006\000\030\003\
\\008\000\030\003\010\000\030\003\011\000\030\003\012\000\030\003\
\\013\000\030\003\014\000\030\003\015\000\030\003\017\000\030\003\
\\018\000\030\003\021\000\030\003\023\000\030\003\024\000\030\003\
\\025\000\030\003\026\000\030\003\027\000\030\003\028\000\030\003\
\\029\000\030\003\030\000\030\003\031\000\030\003\032\000\030\003\
\\033\000\030\003\034\000\030\003\051\000\030\003\052\000\030\003\
\\053\000\030\003\054\000\030\003\055\000\030\003\056\000\030\003\
\\057\000\030\003\058\000\030\003\059\000\030\003\060\000\030\003\
\\061\000\030\003\062\000\030\003\091\000\030\003\000\000\
\\001\000\002\000\031\003\003\000\031\003\004\000\031\003\005\000\206\000\
\\006\000\031\003\008\000\031\003\009\000\205\000\010\000\031\003\
\\011\000\031\003\012\000\031\003\013\000\031\003\014\000\031\003\
\\015\000\031\003\016\000\204\000\017\000\031\003\018\000\031\003\
\\021\000\031\003\023\000\031\003\024\000\031\003\025\000\031\003\
\\026\000\031\003\027\000\031\003\028\000\031\003\029\000\031\003\
\\030\000\031\003\031\000\031\003\032\000\031\003\033\000\031\003\
\\034\000\031\003\051\000\031\003\052\000\031\003\053\000\031\003\
\\054\000\031\003\055\000\031\003\056\000\031\003\057\000\031\003\
\\058\000\031\003\059\000\031\003\060\000\031\003\061\000\031\003\
\\062\000\031\003\072\000\203\000\091\000\031\003\000\000\
\\001\000\002\000\031\003\003\000\031\003\004\000\031\003\005\000\206\000\
\\009\000\205\000\012\000\031\003\014\000\031\003\015\000\055\003\
\\016\000\204\000\017\000\031\003\018\000\031\003\021\000\031\003\
\\023\000\055\003\024\000\055\003\025\000\055\003\026\000\055\003\
\\027\000\055\003\028\000\055\003\029\000\055\003\030\000\055\003\
\\031\000\055\003\032\000\055\003\033\000\055\003\034\000\055\003\
\\051\000\031\003\052\000\031\003\053\000\031\003\054\000\031\003\
\\055\000\031\003\056\000\031\003\057\000\031\003\058\000\031\003\
\\059\000\031\003\060\000\031\003\061\000\031\003\062\000\031\003\
\\072\000\203\000\000\000\
\\001\000\002\000\032\003\003\000\032\003\004\000\032\003\006\000\032\003\
\\008\000\032\003\010\000\032\003\011\000\032\003\012\000\032\003\
\\013\000\032\003\014\000\032\003\015\000\032\003\017\000\032\003\
\\018\000\032\003\021\000\032\003\023\000\032\003\024\000\032\003\
\\025\000\032\003\026\000\032\003\027\000\032\003\028\000\032\003\
\\029\000\032\003\030\000\032\003\031\000\032\003\032\000\032\003\
\\033\000\032\003\034\000\032\003\051\000\032\003\052\000\032\003\
\\053\000\032\003\054\000\032\003\055\000\032\003\056\000\032\003\
\\057\000\032\003\058\000\032\003\059\000\032\003\060\000\032\003\
\\061\000\032\003\062\000\032\003\091\000\032\003\000\000\
\\001\000\002\000\033\003\003\000\033\003\004\000\033\003\006\000\033\003\
\\008\000\033\003\010\000\033\003\011\000\033\003\012\000\033\003\
\\013\000\033\003\014\000\033\003\015\000\033\003\017\000\033\003\
\\018\000\033\003\021\000\033\003\023\000\033\003\024\000\033\003\
\\025\000\033\003\026\000\033\003\027\000\033\003\028\000\033\003\
\\029\000\033\003\030\000\033\003\031\000\033\003\032\000\033\003\
\\033\000\033\003\034\000\033\003\051\000\033\003\052\000\033\003\
\\053\000\033\003\054\000\033\003\055\000\033\003\056\000\033\003\
\\057\000\033\003\058\000\033\003\059\000\033\003\060\000\033\003\
\\061\000\033\003\062\000\033\003\091\000\033\003\000\000\
\\001\000\002\000\034\003\003\000\034\003\004\000\034\003\006\000\034\003\
\\008\000\034\003\010\000\034\003\011\000\034\003\012\000\034\003\
\\013\000\034\003\014\000\034\003\015\000\034\003\017\000\034\003\
\\018\000\034\003\021\000\034\003\023\000\034\003\024\000\034\003\
\\025\000\034\003\026\000\034\003\027\000\034\003\028\000\034\003\
\\029\000\034\003\030\000\034\003\031\000\034\003\032\000\034\003\
\\033\000\034\003\034\000\034\003\051\000\034\003\052\000\034\003\
\\053\000\034\003\054\000\034\003\055\000\034\003\056\000\034\003\
\\057\000\034\003\058\000\034\003\059\000\034\003\060\000\034\003\
\\061\000\034\003\062\000\034\003\091\000\034\003\000\000\
\\001\000\002\000\035\003\003\000\035\003\004\000\035\003\006\000\035\003\
\\008\000\035\003\010\000\035\003\011\000\035\003\012\000\035\003\
\\013\000\035\003\014\000\035\003\015\000\035\003\017\000\035\003\
\\018\000\035\003\021\000\035\003\023\000\035\003\024\000\035\003\
\\025\000\035\003\026\000\035\003\027\000\035\003\028\000\035\003\
\\029\000\035\003\030\000\035\003\031\000\035\003\032\000\035\003\
\\033\000\035\003\034\000\035\003\051\000\035\003\052\000\035\003\
\\053\000\035\003\054\000\035\003\055\000\035\003\056\000\035\003\
\\057\000\035\003\058\000\035\003\059\000\035\003\060\000\035\003\
\\061\000\035\003\062\000\035\003\091\000\035\003\000\000\
\\001\000\002\000\036\003\003\000\036\003\004\000\036\003\006\000\036\003\
\\008\000\036\003\010\000\036\003\011\000\036\003\012\000\036\003\
\\013\000\036\003\014\000\036\003\015\000\036\003\017\000\036\003\
\\018\000\036\003\021\000\036\003\023\000\036\003\024\000\036\003\
\\025\000\036\003\026\000\036\003\027\000\036\003\028\000\036\003\
\\029\000\036\003\030\000\036\003\031\000\036\003\032\000\036\003\
\\033\000\036\003\034\000\036\003\051\000\036\003\052\000\036\003\
\\053\000\036\003\054\000\036\003\055\000\036\003\056\000\036\003\
\\057\000\036\003\058\000\036\003\059\000\036\003\060\000\036\003\
\\061\000\036\003\062\000\036\003\091\000\036\003\000\000\
\\001\000\002\000\036\003\003\000\036\003\004\000\036\003\012\000\036\003\
\\014\000\036\003\015\000\056\003\017\000\036\003\018\000\036\003\
\\021\000\036\003\023\000\056\003\024\000\056\003\025\000\056\003\
\\026\000\056\003\027\000\056\003\028\000\056\003\029\000\056\003\
\\030\000\056\003\031\000\056\003\032\000\056\003\033\000\056\003\
\\034\000\056\003\051\000\036\003\052\000\036\003\053\000\036\003\
\\054\000\036\003\055\000\036\003\056\000\036\003\057\000\036\003\
\\058\000\036\003\059\000\036\003\060\000\036\003\061\000\036\003\
\\062\000\036\003\000\000\
\\001\000\002\000\037\003\003\000\037\003\004\000\037\003\006\000\037\003\
\\008\000\037\003\010\000\037\003\011\000\037\003\012\000\037\003\
\\013\000\037\003\014\000\037\003\015\000\037\003\017\000\037\003\
\\018\000\037\003\021\000\037\003\023\000\037\003\024\000\037\003\
\\025\000\037\003\026\000\037\003\027\000\037\003\028\000\037\003\
\\029\000\037\003\030\000\037\003\031\000\037\003\032\000\037\003\
\\033\000\037\003\034\000\037\003\051\000\037\003\052\000\037\003\
\\053\000\037\003\054\000\037\003\055\000\037\003\056\000\037\003\
\\057\000\037\003\058\000\037\003\059\000\037\003\060\000\037\003\
\\061\000\037\003\062\000\037\003\091\000\037\003\000\000\
\\001\000\002\000\038\003\003\000\038\003\004\000\038\003\006\000\038\003\
\\007\000\148\001\008\000\038\003\010\000\038\003\011\000\038\003\
\\012\000\038\003\013\000\038\003\014\000\038\003\015\000\038\003\
\\017\000\038\003\018\000\038\003\021\000\038\003\023\000\038\003\
\\024\000\038\003\025\000\038\003\026\000\038\003\027\000\038\003\
\\028\000\038\003\029\000\038\003\030\000\038\003\031\000\038\003\
\\032\000\038\003\033\000\038\003\034\000\038\003\051\000\038\003\
\\052\000\038\003\053\000\038\003\054\000\038\003\055\000\038\003\
\\056\000\038\003\057\000\038\003\058\000\038\003\059\000\038\003\
\\060\000\038\003\061\000\038\003\062\000\038\003\091\000\038\003\000\000\
\\001\000\002\000\039\003\003\000\039\003\004\000\039\003\006\000\039\003\
\\008\000\039\003\010\000\039\003\011\000\039\003\012\000\039\003\
\\013\000\039\003\014\000\039\003\015\000\039\003\017\000\039\003\
\\018\000\039\003\021\000\039\003\023\000\039\003\024\000\039\003\
\\025\000\039\003\026\000\039\003\027\000\039\003\028\000\039\003\
\\029\000\039\003\030\000\039\003\031\000\039\003\032\000\039\003\
\\033\000\039\003\034\000\039\003\051\000\039\003\052\000\039\003\
\\053\000\039\003\054\000\039\003\055\000\039\003\056\000\039\003\
\\057\000\039\003\058\000\039\003\059\000\039\003\060\000\039\003\
\\061\000\039\003\062\000\039\003\091\000\039\003\000\000\
\\001\000\002\000\042\003\003\000\042\003\004\000\042\003\005\000\042\003\
\\006\000\042\003\008\000\042\003\009\000\042\003\010\000\042\003\
\\011\000\042\003\012\000\042\003\013\000\042\003\014\000\042\003\
\\015\000\042\003\016\000\042\003\017\000\042\003\018\000\042\003\
\\021\000\042\003\023\000\042\003\024\000\042\003\025\000\042\003\
\\026\000\042\003\027\000\042\003\028\000\042\003\029\000\042\003\
\\030\000\042\003\031\000\042\003\032\000\042\003\033\000\042\003\
\\034\000\042\003\051\000\042\003\052\000\042\003\053\000\042\003\
\\054\000\042\003\055\000\042\003\056\000\042\003\057\000\042\003\
\\058\000\042\003\059\000\042\003\060\000\042\003\061\000\042\003\
\\062\000\042\003\072\000\042\003\091\000\042\003\000\000\
\\001\000\002\000\043\003\003\000\043\003\004\000\043\003\005\000\043\003\
\\006\000\043\003\008\000\043\003\009\000\043\003\010\000\043\003\
\\011\000\043\003\012\000\043\003\013\000\043\003\014\000\043\003\
\\015\000\043\003\016\000\043\003\017\000\043\003\018\000\043\003\
\\021\000\043\003\023\000\043\003\024\000\043\003\025\000\043\003\
\\026\000\043\003\027\000\043\003\028\000\043\003\029\000\043\003\
\\030\000\043\003\031\000\043\003\032\000\043\003\033\000\043\003\
\\034\000\043\003\051\000\043\003\052\000\043\003\053\000\043\003\
\\054\000\043\003\055\000\043\003\056\000\043\003\057\000\043\003\
\\058\000\043\003\059\000\043\003\060\000\043\003\061\000\043\003\
\\062\000\043\003\072\000\043\003\091\000\043\003\000\000\
\\001\000\002\000\044\003\003\000\044\003\004\000\044\003\005\000\044\003\
\\006\000\044\003\008\000\044\003\009\000\044\003\010\000\044\003\
\\011\000\044\003\012\000\044\003\013\000\044\003\014\000\044\003\
\\015\000\044\003\016\000\044\003\017\000\044\003\018\000\044\003\
\\021\000\044\003\023\000\044\003\024\000\044\003\025\000\044\003\
\\026\000\044\003\027\000\044\003\028\000\044\003\029\000\044\003\
\\030\000\044\003\031\000\044\003\032\000\044\003\033\000\044\003\
\\034\000\044\003\051\000\044\003\052\000\044\003\053\000\044\003\
\\054\000\044\003\055\000\044\003\056\000\044\003\057\000\044\003\
\\058\000\044\003\059\000\044\003\060\000\044\003\061\000\044\003\
\\062\000\044\003\072\000\044\003\091\000\044\003\000\000\
\\001\000\002\000\045\003\003\000\045\003\004\000\045\003\005\000\045\003\
\\006\000\045\003\008\000\045\003\009\000\045\003\010\000\045\003\
\\011\000\045\003\012\000\045\003\013\000\045\003\014\000\045\003\
\\015\000\045\003\016\000\045\003\017\000\045\003\018\000\045\003\
\\021\000\045\003\023\000\045\003\024\000\045\003\025\000\045\003\
\\026\000\045\003\027\000\045\003\028\000\045\003\029\000\045\003\
\\030\000\045\003\031\000\045\003\032\000\045\003\033\000\045\003\
\\034\000\045\003\051\000\045\003\052\000\045\003\053\000\045\003\
\\054\000\045\003\055\000\045\003\056\000\045\003\057\000\045\003\
\\058\000\045\003\059\000\045\003\060\000\045\003\061\000\045\003\
\\062\000\045\003\072\000\045\003\091\000\045\003\000\000\
\\001\000\002\000\046\003\003\000\046\003\004\000\046\003\005\000\046\003\
\\006\000\046\003\008\000\046\003\009\000\046\003\010\000\046\003\
\\011\000\046\003\012\000\046\003\013\000\046\003\014\000\046\003\
\\015\000\046\003\016\000\046\003\017\000\046\003\018\000\046\003\
\\021\000\046\003\023\000\046\003\024\000\046\003\025\000\046\003\
\\026\000\046\003\027\000\046\003\028\000\046\003\029\000\046\003\
\\030\000\046\003\031\000\046\003\032\000\046\003\033\000\046\003\
\\034\000\046\003\051\000\046\003\052\000\046\003\053\000\046\003\
\\054\000\046\003\055\000\046\003\056\000\046\003\057\000\046\003\
\\058\000\046\003\059\000\046\003\060\000\046\003\061\000\046\003\
\\062\000\046\003\072\000\046\003\091\000\046\003\000\000\
\\001\000\002\000\047\003\003\000\047\003\004\000\047\003\005\000\047\003\
\\006\000\047\003\008\000\047\003\009\000\047\003\010\000\047\003\
\\011\000\047\003\012\000\047\003\013\000\047\003\014\000\047\003\
\\015\000\047\003\016\000\047\003\017\000\047\003\018\000\047\003\
\\021\000\047\003\023\000\047\003\024\000\047\003\025\000\047\003\
\\026\000\047\003\027\000\047\003\028\000\047\003\029\000\047\003\
\\030\000\047\003\031\000\047\003\032\000\047\003\033\000\047\003\
\\034\000\047\003\051\000\047\003\052\000\047\003\053\000\047\003\
\\054\000\047\003\055\000\047\003\056\000\047\003\057\000\047\003\
\\058\000\047\003\059\000\047\003\060\000\047\003\061\000\047\003\
\\062\000\047\003\072\000\047\003\091\000\047\003\000\000\
\\001\000\002\000\048\003\003\000\048\003\004\000\048\003\005\000\048\003\
\\006\000\048\003\008\000\048\003\009\000\048\003\010\000\048\003\
\\011\000\048\003\012\000\048\003\013\000\048\003\014\000\048\003\
\\015\000\048\003\016\000\048\003\017\000\048\003\018\000\048\003\
\\021\000\048\003\023\000\048\003\024\000\048\003\025\000\048\003\
\\026\000\048\003\027\000\048\003\028\000\048\003\029\000\048\003\
\\030\000\048\003\031\000\048\003\032\000\048\003\033\000\048\003\
\\034\000\048\003\051\000\048\003\052\000\048\003\053\000\048\003\
\\054\000\048\003\055\000\048\003\056\000\048\003\057\000\048\003\
\\058\000\048\003\059\000\048\003\060\000\048\003\061\000\048\003\
\\062\000\048\003\072\000\048\003\091\000\048\003\000\000\
\\001\000\002\000\048\003\003\000\048\003\004\000\048\003\005\000\048\003\
\\009\000\048\003\012\000\048\003\013\000\184\002\014\000\048\003\
\\015\000\048\003\016\000\048\003\017\000\048\003\018\000\048\003\
\\021\000\048\003\023\000\048\003\024\000\048\003\025\000\048\003\
\\026\000\048\003\027\000\048\003\028\000\048\003\029\000\048\003\
\\030\000\048\003\031\000\048\003\032\000\048\003\033\000\048\003\
\\034\000\048\003\051\000\048\003\052\000\048\003\053\000\048\003\
\\054\000\048\003\055\000\048\003\056\000\048\003\057\000\048\003\
\\058\000\048\003\059\000\048\003\060\000\048\003\061\000\048\003\
\\062\000\048\003\072\000\048\003\000\000\
\\001\000\002\000\049\003\003\000\049\003\004\000\049\003\005\000\049\003\
\\006\000\049\003\008\000\049\003\009\000\049\003\010\000\049\003\
\\011\000\049\003\012\000\049\003\013\000\049\003\014\000\049\003\
\\015\000\049\003\016\000\049\003\017\000\049\003\018\000\049\003\
\\021\000\049\003\023\000\049\003\024\000\049\003\025\000\049\003\
\\026\000\049\003\027\000\049\003\028\000\049\003\029\000\049\003\
\\030\000\049\003\031\000\049\003\032\000\049\003\033\000\049\003\
\\034\000\049\003\051\000\049\003\052\000\049\003\053\000\049\003\
\\054\000\049\003\055\000\049\003\056\000\049\003\057\000\049\003\
\\058\000\049\003\059\000\049\003\060\000\049\003\061\000\049\003\
\\062\000\049\003\072\000\049\003\091\000\049\003\000\000\
\\001\000\002\000\050\003\003\000\050\003\004\000\050\003\005\000\050\003\
\\006\000\050\003\008\000\050\003\009\000\050\003\010\000\050\003\
\\011\000\050\003\012\000\050\003\013\000\050\003\014\000\050\003\
\\015\000\050\003\016\000\050\003\017\000\050\003\018\000\050\003\
\\021\000\050\003\023\000\050\003\024\000\050\003\025\000\050\003\
\\026\000\050\003\027\000\050\003\028\000\050\003\029\000\050\003\
\\030\000\050\003\031\000\050\003\032\000\050\003\033\000\050\003\
\\034\000\050\003\051\000\050\003\052\000\050\003\053\000\050\003\
\\054\000\050\003\055\000\050\003\056\000\050\003\057\000\050\003\
\\058\000\050\003\059\000\050\003\060\000\050\003\061\000\050\003\
\\062\000\050\003\072\000\050\003\091\000\050\003\000\000\
\\001\000\002\000\051\003\003\000\051\003\004\000\051\003\005\000\051\003\
\\006\000\051\003\008\000\051\003\009\000\051\003\010\000\051\003\
\\011\000\051\003\012\000\051\003\013\000\051\003\014\000\051\003\
\\015\000\051\003\016\000\051\003\017\000\051\003\018\000\051\003\
\\021\000\051\003\023\000\051\003\024\000\051\003\025\000\051\003\
\\026\000\051\003\027\000\051\003\028\000\051\003\029\000\051\003\
\\030\000\051\003\031\000\051\003\032\000\051\003\033\000\051\003\
\\034\000\051\003\051\000\051\003\052\000\051\003\053\000\051\003\
\\054\000\051\003\055\000\051\003\056\000\051\003\057\000\051\003\
\\058\000\051\003\059\000\051\003\060\000\051\003\061\000\051\003\
\\062\000\051\003\072\000\051\003\091\000\051\003\099\000\202\000\000\000\
\\001\000\002\000\052\003\003\000\052\003\004\000\052\003\005\000\052\003\
\\006\000\052\003\008\000\052\003\009\000\052\003\010\000\052\003\
\\011\000\052\003\012\000\052\003\013\000\052\003\014\000\052\003\
\\015\000\052\003\016\000\052\003\017\000\052\003\018\000\052\003\
\\021\000\052\003\023\000\052\003\024\000\052\003\025\000\052\003\
\\026\000\052\003\027\000\052\003\028\000\052\003\029\000\052\003\
\\030\000\052\003\031\000\052\003\032\000\052\003\033\000\052\003\
\\034\000\052\003\051\000\052\003\052\000\052\003\053\000\052\003\
\\054\000\052\003\055\000\052\003\056\000\052\003\057\000\052\003\
\\058\000\052\003\059\000\052\003\060\000\052\003\061\000\052\003\
\\062\000\052\003\072\000\052\003\091\000\052\003\099\000\052\003\000\000\
\\001\000\002\000\053\003\003\000\053\003\004\000\053\003\005\000\053\003\
\\006\000\053\003\008\000\053\003\009\000\053\003\010\000\053\003\
\\011\000\053\003\012\000\053\003\013\000\053\003\014\000\053\003\
\\015\000\053\003\016\000\053\003\017\000\053\003\018\000\053\003\
\\021\000\053\003\023\000\053\003\024\000\053\003\025\000\053\003\
\\026\000\053\003\027\000\053\003\028\000\053\003\029\000\053\003\
\\030\000\053\003\031\000\053\003\032\000\053\003\033\000\053\003\
\\034\000\053\003\051\000\053\003\052\000\053\003\053\000\053\003\
\\054\000\053\003\055\000\053\003\056\000\053\003\057\000\053\003\
\\058\000\053\003\059\000\053\003\060\000\053\003\061\000\053\003\
\\062\000\053\003\072\000\053\003\091\000\053\003\099\000\053\003\000\000\
\\001\000\002\000\054\003\003\000\054\003\004\000\054\003\005\000\054\003\
\\006\000\054\003\008\000\054\003\009\000\054\003\010\000\054\003\
\\011\000\054\003\012\000\054\003\013\000\054\003\014\000\054\003\
\\015\000\054\003\016\000\054\003\017\000\054\003\018\000\054\003\
\\021\000\054\003\023\000\054\003\024\000\054\003\025\000\054\003\
\\026\000\054\003\027\000\054\003\028\000\054\003\029\000\054\003\
\\030\000\054\003\031\000\054\003\032\000\054\003\033\000\054\003\
\\034\000\054\003\051\000\054\003\052\000\054\003\053\000\054\003\
\\054\000\054\003\055\000\054\003\056\000\054\003\057\000\054\003\
\\058\000\054\003\059\000\054\003\060\000\054\003\061\000\054\003\
\\062\000\054\003\072\000\054\003\091\000\054\003\000\000\
\\001\000\002\000\058\000\005\000\099\002\006\000\099\002\009\000\099\002\
\\011\000\099\002\073\000\099\002\080\000\031\000\081\000\030\000\
\\082\000\029\000\095\000\099\002\101\000\099\002\000\000\
\\001\000\002\000\058\000\005\000\100\002\006\000\100\002\009\000\100\002\
\\011\000\100\002\073\000\100\002\095\000\100\002\101\000\100\002\000\000\
\\001\000\002\000\058\000\005\000\057\000\012\000\056\000\073\000\055\000\000\000\
\\001\000\002\000\058\000\005\000\057\000\073\000\055\000\000\000\
\\001\000\002\000\058\000\005\000\251\000\006\000\063\002\009\000\250\000\
\\035\000\047\000\049\000\046\000\063\000\045\000\064\000\044\000\
\\065\000\043\000\066\000\042\000\067\000\041\000\068\000\040\000\
\\069\000\039\000\070\000\038\000\071\000\037\000\073\000\055\000\
\\074\000\036\000\076\000\035\000\077\000\034\000\078\000\033\000\
\\079\000\032\000\080\000\031\000\081\000\030\000\082\000\029\000\
\\084\000\028\000\085\000\027\000\086\000\026\000\087\000\025\000\
\\088\000\024\000\089\000\023\000\090\000\022\000\093\000\021\000\
\\095\000\020\000\098\000\019\000\101\000\018\000\103\000\017\000\000\000\
\\001\000\002\000\058\000\005\000\251\000\006\000\069\002\009\000\250\000\
\\011\000\069\002\073\000\055\000\000\000\
\\001\000\002\000\058\000\005\000\084\001\006\000\063\002\009\000\250\000\
\\035\000\047\000\049\000\046\000\063\000\045\000\064\000\044\000\
\\065\000\043\000\066\000\042\000\067\000\041\000\068\000\040\000\
\\069\000\039\000\070\000\038\000\071\000\037\000\074\000\036\000\
\\076\000\035\000\077\000\034\000\078\000\033\000\079\000\032\000\
\\080\000\031\000\081\000\030\000\082\000\029\000\084\000\028\000\
\\085\000\027\000\086\000\026\000\087\000\025\000\088\000\024\000\
\\089\000\023\000\090\000\022\000\093\000\021\000\095\000\020\000\
\\098\000\019\000\101\000\018\000\103\000\017\000\000\000\
\\001\000\002\000\058\000\005\000\084\001\006\000\160\002\009\000\250\000\000\000\
\\001\000\002\000\102\000\000\000\
\\001\000\002\000\139\000\005\000\138\000\006\000\251\002\018\000\137\000\
\\020\000\136\000\021\000\135\000\022\000\134\000\048\000\133\000\
\\050\000\132\000\073\000\131\000\075\000\130\000\099\000\129\000\000\000\
\\001\000\002\000\139\000\005\000\138\000\006\000\136\001\018\000\137\000\
\\020\000\136\000\021\000\135\000\022\000\134\000\048\000\133\000\
\\050\000\132\000\073\000\131\000\075\000\130\000\099\000\129\000\000\000\
\\001\000\002\000\139\000\005\000\138\000\007\000\155\000\008\000\162\002\
\\009\000\003\001\016\000\002\001\018\000\137\000\020\000\136\000\
\\021\000\135\000\022\000\134\000\048\000\133\000\050\000\132\000\
\\073\000\131\000\075\000\130\000\099\000\129\000\000\000\
\\001\000\002\000\139\000\005\000\138\000\007\000\155\000\009\000\003\001\
\\016\000\002\001\018\000\137\000\020\000\136\000\021\000\135\000\
\\022\000\134\000\048\000\133\000\050\000\132\000\073\000\131\000\
\\075\000\130\000\099\000\129\000\000\000\
\\001\000\002\000\139\000\005\000\138\000\007\000\155\000\018\000\137\000\
\\020\000\136\000\021\000\135\000\022\000\134\000\048\000\133\000\
\\050\000\132\000\073\000\131\000\075\000\130\000\099\000\129\000\000\000\
\\001\000\002\000\139\000\005\000\138\000\007\000\148\001\018\000\137\000\
\\020\000\136\000\021\000\135\000\022\000\134\000\048\000\133\000\
\\050\000\132\000\073\000\131\000\075\000\130\000\099\000\129\000\000\000\
\\001\000\002\000\139\000\005\000\138\000\010\000\146\000\018\000\137\000\
\\020\000\136\000\021\000\135\000\022\000\134\000\048\000\133\000\
\\050\000\132\000\073\000\131\000\075\000\130\000\099\000\129\000\000\000\
\\001\000\002\000\139\000\005\000\138\000\010\000\098\001\018\000\137\000\
\\020\000\136\000\021\000\135\000\022\000\134\000\048\000\133\000\
\\050\000\132\000\073\000\131\000\075\000\130\000\099\000\129\000\000\000\
\\001\000\002\000\139\000\005\000\138\000\012\000\241\002\018\000\137\000\
\\020\000\136\000\021\000\135\000\022\000\134\000\048\000\133\000\
\\050\000\132\000\073\000\131\000\075\000\130\000\099\000\129\000\000\000\
\\001\000\002\000\139\000\005\000\138\000\012\000\034\001\018\000\137\000\
\\020\000\136\000\021\000\135\000\022\000\134\000\048\000\133\000\
\\050\000\132\000\073\000\131\000\075\000\130\000\099\000\129\000\000\000\
\\001\000\002\000\139\000\005\000\138\000\018\000\137\000\020\000\136\000\
\\021\000\135\000\022\000\134\000\035\000\047\000\048\000\133\000\
\\049\000\046\000\050\000\132\000\063\000\045\000\064\000\044\000\
\\065\000\043\000\066\000\042\000\067\000\041\000\068\000\040\000\
\\069\000\039\000\070\000\038\000\071\000\037\000\073\000\131\000\
\\074\000\036\000\075\000\130\000\076\000\035\000\077\000\034\000\
\\080\000\031\000\081\000\030\000\082\000\029\000\099\000\129\000\000\000\
\\001\000\002\000\139\000\005\000\138\000\018\000\137\000\020\000\136\000\
\\021\000\135\000\022\000\134\000\048\000\133\000\050\000\132\000\
\\073\000\131\000\075\000\130\000\099\000\129\000\000\000\
\\001\000\002\000\139\000\005\000\229\000\018\000\137\000\020\000\136\000\
\\021\000\135\000\022\000\134\000\048\000\133\000\050\000\132\000\
\\073\000\131\000\075\000\130\000\099\000\129\000\000\000\
\\001\000\002\000\181\000\005\000\138\000\007\000\092\000\008\000\071\002\
\\012\000\180\000\018\000\137\000\020\000\136\000\021\000\135\000\
\\022\000\134\000\035\000\047\000\036\000\179\000\038\000\178\000\
\\039\000\177\000\040\000\176\000\041\000\175\000\042\000\174\000\
\\043\000\173\000\044\000\172\000\045\000\171\000\046\000\071\002\
\\047\000\071\002\048\000\133\000\049\000\046\000\050\000\132\000\
\\063\000\045\000\064\000\044\000\065\000\043\000\066\000\042\000\
\\067\000\041\000\068\000\040\000\069\000\039\000\070\000\038\000\
\\071\000\037\000\073\000\170\000\074\000\036\000\075\000\130\000\
\\076\000\035\000\077\000\034\000\078\000\033\000\079\000\032\000\
\\080\000\031\000\081\000\030\000\082\000\029\000\084\000\028\000\
\\085\000\027\000\086\000\026\000\087\000\025\000\088\000\024\000\
\\089\000\023\000\090\000\022\000\091\000\169\000\092\000\168\000\
\\093\000\021\000\095\000\020\000\096\000\167\000\098\000\019\000\
\\099\000\129\000\101\000\018\000\102\000\166\000\103\000\017\000\000\000\
\\001\000\002\000\181\000\005\000\138\000\007\000\092\000\008\000\071\002\
\\012\000\180\000\018\000\137\000\020\000\136\000\021\000\135\000\
\\022\000\134\000\035\000\047\000\036\000\179\000\038\000\178\000\
\\039\000\177\000\040\000\176\000\041\000\175\000\042\000\174\000\
\\043\000\173\000\044\000\172\000\045\000\171\000\048\000\133\000\
\\049\000\046\000\050\000\132\000\063\000\045\000\064\000\044\000\
\\065\000\043\000\066\000\042\000\067\000\041\000\068\000\040\000\
\\069\000\039\000\070\000\038\000\071\000\037\000\073\000\170\000\
\\074\000\036\000\075\000\130\000\076\000\035\000\077\000\034\000\
\\078\000\033\000\079\000\032\000\080\000\031\000\081\000\030\000\
\\082\000\029\000\084\000\028\000\085\000\027\000\086\000\026\000\
\\087\000\025\000\088\000\024\000\089\000\023\000\090\000\022\000\
\\091\000\169\000\092\000\168\000\093\000\021\000\095\000\020\000\
\\096\000\167\000\098\000\019\000\099\000\129\000\101\000\018\000\
\\102\000\166\000\103\000\017\000\000\000\
\\001\000\002\000\181\000\005\000\138\000\007\000\092\000\012\000\180\000\
\\018\000\137\000\020\000\136\000\021\000\135\000\022\000\134\000\
\\036\000\179\000\038\000\178\000\039\000\177\000\040\000\176\000\
\\041\000\175\000\042\000\174\000\043\000\173\000\044\000\172\000\
\\045\000\171\000\048\000\133\000\050\000\132\000\073\000\170\000\
\\075\000\130\000\091\000\169\000\092\000\168\000\096\000\167\000\
\\097\000\075\002\099\000\129\000\102\000\166\000\000\000\
\\001\000\002\000\181\000\005\000\138\000\007\000\092\000\012\000\180\000\
\\018\000\137\000\020\000\136\000\021\000\135\000\022\000\134\000\
\\036\000\179\000\038\000\178\000\039\000\177\000\040\000\176\000\
\\041\000\175\000\042\000\174\000\043\000\173\000\044\000\172\000\
\\045\000\171\000\048\000\133\000\050\000\132\000\073\000\170\000\
\\075\000\130\000\091\000\169\000\092\000\168\000\096\000\167\000\
\\097\000\077\002\099\000\129\000\102\000\166\000\000\000\
\\001\000\002\000\181\000\005\000\138\000\007\000\092\000\012\000\180\000\
\\018\000\137\000\020\000\136\000\021\000\135\000\022\000\134\000\
\\036\000\179\000\038\000\178\000\039\000\177\000\040\000\176\000\
\\041\000\175\000\042\000\174\000\043\000\173\000\044\000\172\000\
\\045\000\171\000\048\000\133\000\050\000\132\000\073\000\170\000\
\\075\000\130\000\091\000\169\000\092\000\168\000\096\000\167\000\
\\099\000\129\000\102\000\166\000\000\000\
\\001\000\002\000\209\000\003\000\208\000\004\000\207\000\006\000\022\003\
\\008\000\022\003\010\000\022\003\011\000\022\003\012\000\022\003\
\\013\000\022\003\014\000\022\003\017\000\022\003\018\000\022\003\
\\021\000\022\003\051\000\022\003\052\000\022\003\053\000\022\003\
\\054\000\022\003\055\000\022\003\056\000\022\003\057\000\022\003\
\\058\000\022\003\059\000\022\003\060\000\022\003\061\000\022\003\
\\062\000\022\003\091\000\022\003\000\000\
\\001\000\002\000\209\000\003\000\208\000\004\000\207\000\006\000\023\003\
\\008\000\023\003\010\000\023\003\011\000\023\003\012\000\023\003\
\\013\000\023\003\014\000\023\003\017\000\023\003\018\000\023\003\
\\021\000\023\003\051\000\023\003\052\000\023\003\053\000\023\003\
\\054\000\023\003\055\000\023\003\056\000\023\003\057\000\023\003\
\\058\000\023\003\059\000\023\003\060\000\023\003\061\000\023\003\
\\062\000\023\003\091\000\023\003\000\000\
\\001\000\002\000\209\000\003\000\208\000\004\000\207\000\006\000\024\003\
\\008\000\024\003\010\000\024\003\011\000\024\003\012\000\024\003\
\\013\000\024\003\014\000\024\003\017\000\024\003\018\000\024\003\
\\021\000\024\003\051\000\024\003\052\000\024\003\053\000\024\003\
\\054\000\024\003\055\000\024\003\056\000\024\003\057\000\024\003\
\\058\000\024\003\059\000\024\003\060\000\024\003\061\000\024\003\
\\062\000\024\003\091\000\024\003\000\000\
\\001\000\002\000\125\001\005\000\124\001\006\000\243\002\073\000\131\000\
\\075\000\130\000\099\000\129\000\000\000\
\\001\000\002\000\125\001\005\000\124\001\012\000\236\002\035\000\047\000\
\\049\000\046\000\063\000\045\000\064\000\044\000\065\000\043\000\
\\066\000\042\000\067\000\041\000\068\000\040\000\069\000\039\000\
\\070\000\038\000\071\000\037\000\073\000\131\000\074\000\036\000\
\\075\000\130\000\076\000\035\000\077\000\034\000\078\000\033\000\
\\079\000\032\000\080\000\031\000\081\000\030\000\082\000\029\000\
\\084\000\028\000\085\000\027\000\086\000\026\000\087\000\025\000\
\\088\000\024\000\089\000\023\000\090\000\022\000\093\000\021\000\
\\095\000\020\000\098\000\019\000\099\000\129\000\101\000\018\000\
\\103\000\017\000\000\000\
\\001\000\002\000\125\001\005\000\124\001\073\000\131\000\075\000\130\000\
\\099\000\129\000\000\000\
\\001\000\005\000\101\002\006\000\101\002\009\000\101\002\011\000\101\002\
\\073\000\101\002\095\000\101\002\101\000\101\002\000\000\
\\001\000\005\000\102\002\006\000\102\002\009\000\102\002\011\000\102\002\
\\073\000\102\002\095\000\102\002\101\000\102\002\000\000\
\\001\000\005\000\106\002\006\000\106\002\007\000\106\002\009\000\106\002\
\\011\000\106\002\012\000\106\002\013\000\106\002\015\000\106\002\
\\095\000\106\002\101\000\106\002\102\000\106\002\000\000\
\\001\000\005\000\107\002\006\000\107\002\007\000\107\002\009\000\107\002\
\\011\000\107\002\012\000\107\002\013\000\107\002\015\000\107\002\
\\094\000\092\001\095\000\107\002\101\000\107\002\102\000\107\002\000\000\
\\001\000\005\000\108\002\006\000\108\002\007\000\108\002\009\000\108\002\
\\011\000\108\002\012\000\108\002\013\000\108\002\015\000\108\002\
\\095\000\108\002\101\000\108\002\102\000\108\002\000\000\
\\001\000\005\000\109\002\006\000\109\002\007\000\109\002\009\000\109\002\
\\011\000\109\002\012\000\109\002\013\000\109\002\015\000\109\002\
\\095\000\109\002\101\000\109\002\102\000\109\002\000\000\
\\001\000\005\000\110\002\006\000\110\002\007\000\110\002\009\000\110\002\
\\011\000\110\002\012\000\110\002\013\000\110\002\015\000\110\002\
\\095\000\110\002\101\000\110\002\102\000\110\002\000\000\
\\001\000\005\000\111\002\006\000\111\002\007\000\111\002\009\000\111\002\
\\011\000\111\002\012\000\111\002\013\000\111\002\015\000\111\002\
\\095\000\111\002\101\000\111\002\102\000\111\002\000\000\
\\001\000\005\000\112\002\006\000\112\002\007\000\112\002\009\000\112\002\
\\011\000\112\002\012\000\112\002\013\000\112\002\015\000\112\002\
\\095\000\112\002\101\000\112\002\102\000\112\002\000\000\
\\001\000\005\000\113\002\006\000\113\002\007\000\113\002\009\000\113\002\
\\011\000\113\002\012\000\113\002\013\000\113\002\015\000\113\002\
\\095\000\113\002\101\000\113\002\102\000\113\002\000\000\
\\001\000\005\000\114\002\006\000\114\002\007\000\114\002\009\000\114\002\
\\011\000\114\002\012\000\114\002\013\000\114\002\015\000\114\002\
\\095\000\114\002\101\000\114\002\102\000\114\002\000\000\
\\001\000\005\000\115\002\006\000\115\002\007\000\115\002\009\000\115\002\
\\011\000\115\002\012\000\115\002\013\000\115\002\015\000\115\002\
\\095\000\115\002\101\000\115\002\102\000\115\002\000\000\
\\001\000\005\000\153\002\006\000\153\002\009\000\153\002\011\000\153\002\000\000\
\\001\000\005\000\154\002\006\000\154\002\009\000\154\002\011\000\154\002\000\000\
\\001\000\005\000\155\002\006\000\155\002\009\000\155\002\011\000\155\002\000\000\
\\001\000\005\000\156\002\006\000\156\002\009\000\156\002\011\000\156\002\000\000\
\\001\000\005\000\157\002\006\000\157\002\009\000\157\002\011\000\157\002\000\000\
\\001\000\005\000\158\002\006\000\158\002\009\000\158\002\011\000\158\002\000\000\
\\001\000\005\000\207\002\081\000\023\001\000\000\
\\001\000\005\000\208\002\000\000\
\\001\000\005\000\057\000\073\000\055\000\000\000\
\\001\000\005\000\057\000\073\000\055\000\095\000\020\000\101\000\018\000\000\000\
\\001\000\005\000\065\000\000\000\
\\001\000\005\000\080\000\000\000\
\\001\000\005\000\087\000\006\000\103\002\007\000\103\002\009\000\086\000\
\\011\000\103\002\012\000\103\002\013\000\103\002\015\000\103\002\
\\095\000\020\000\101\000\018\000\102\000\085\000\000\000\
\\001\000\005\000\087\000\006\000\104\002\007\000\104\002\009\000\086\000\
\\011\000\104\002\012\000\104\002\013\000\104\002\015\000\104\002\
\\095\000\020\000\101\000\018\000\102\000\085\000\000\000\
\\001\000\005\000\087\000\006\000\105\002\007\000\105\002\009\000\086\000\
\\011\000\105\002\012\000\105\002\013\000\105\002\015\000\105\002\
\\095\000\020\000\101\000\018\000\102\000\085\000\000\000\
\\001\000\005\000\099\000\000\000\
\\001\000\005\000\144\000\000\000\
\\001\000\005\000\206\000\009\000\205\000\015\000\055\003\016\000\204\000\
\\023\000\055\003\024\000\055\003\025\000\055\003\026\000\055\003\
\\027\000\055\003\028\000\055\003\029\000\055\003\030\000\055\003\
\\031\000\055\003\032\000\055\003\033\000\055\003\034\000\055\003\
\\072\000\203\000\000\000\
\\001\000\005\000\227\000\000\000\
\\001\000\005\000\251\000\006\000\150\002\009\000\250\000\011\000\150\002\
\\073\000\055\000\095\000\020\000\101\000\018\000\000\000\
\\001\000\005\000\027\001\000\000\
\\001\000\005\000\028\001\000\000\
\\001\000\005\000\038\001\000\000\
\\001\000\005\000\039\001\000\000\
\\001\000\005\000\043\001\006\000\034\002\011\000\034\002\000\000\
\\001\000\005\000\084\001\006\000\150\002\009\000\250\000\000\000\
\\001\000\005\000\095\001\006\000\151\002\009\000\094\001\011\000\151\002\000\000\
\\001\000\005\000\095\001\006\000\152\002\009\000\094\001\011\000\152\002\000\000\
\\001\000\005\000\112\001\000\000\
\\001\000\005\000\196\001\000\000\
\\001\000\005\000\227\001\099\000\202\000\000\000\
\\001\000\005\000\007\002\099\000\202\000\000\000\
\\001\000\006\000\031\002\073\000\189\000\080\000\188\000\000\000\
\\001\000\006\000\032\002\011\000\042\001\000\000\
\\001\000\006\000\033\002\000\000\
\\001\000\006\000\035\002\011\000\035\002\000\000\
\\001\000\006\000\036\002\011\000\036\002\000\000\
\\001\000\006\000\037\002\011\000\037\002\000\000\
\\001\000\006\000\038\002\011\000\177\001\000\000\
\\001\000\006\000\039\002\000\000\
\\001\000\006\000\063\002\035\000\047\000\049\000\046\000\063\000\045\000\
\\064\000\044\000\065\000\043\000\066\000\042\000\067\000\041\000\
\\068\000\040\000\069\000\039\000\070\000\038\000\071\000\037\000\
\\074\000\036\000\076\000\035\000\077\000\034\000\078\000\033\000\
\\079\000\032\000\080\000\031\000\081\000\030\000\082\000\029\000\
\\084\000\028\000\085\000\027\000\086\000\026\000\087\000\025\000\
\\088\000\024\000\089\000\023\000\090\000\022\000\093\000\021\000\
\\095\000\020\000\098\000\019\000\101\000\018\000\103\000\017\000\000\000\
\\001\000\006\000\064\002\000\000\
\\001\000\006\000\065\002\011\000\245\000\000\000\
\\001\000\006\000\066\002\000\000\
\\001\000\006\000\067\002\011\000\067\002\000\000\
\\001\000\006\000\068\002\011\000\068\002\000\000\
\\001\000\006\000\159\002\000\000\
\\001\000\006\000\209\002\000\000\
\\001\000\006\000\210\002\013\000\187\001\099\000\202\000\000\000\
\\001\000\006\000\211\002\000\000\
\\001\000\006\000\212\002\013\000\225\001\000\000\
\\001\000\006\000\213\002\000\000\
\\001\000\006\000\214\002\013\000\000\002\000\000\
\\001\000\006\000\215\002\000\000\
\\001\000\006\000\216\002\011\000\008\002\099\000\202\000\000\000\
\\001\000\006\000\217\002\000\000\
\\001\000\006\000\218\002\009\000\207\001\013\000\218\002\099\000\129\000\000\000\
\\001\000\006\000\219\002\013\000\219\002\000\000\
\\001\000\006\000\220\002\011\000\226\001\013\000\220\002\000\000\
\\001\000\006\000\221\002\013\000\221\002\000\000\
\\001\000\006\000\222\002\011\000\222\002\013\000\222\002\000\000\
\\001\000\006\000\223\002\011\000\223\002\013\000\223\002\000\000\
\\001\000\006\000\244\002\000\000\
\\001\000\006\000\245\002\011\000\240\001\091\000\239\001\000\000\
\\001\000\006\000\246\002\000\000\
\\001\000\006\000\247\002\000\000\
\\001\000\006\000\248\002\011\000\248\002\091\000\248\002\000\000\
\\001\000\006\000\249\002\011\000\249\002\091\000\249\002\000\000\
\\001\000\006\000\250\002\011\000\250\002\091\000\250\002\000\000\
\\001\000\006\000\252\002\000\000\
\\001\000\006\000\253\002\011\000\143\001\000\000\
\\001\000\006\000\254\002\000\000\
\\001\000\006\000\255\002\008\000\255\002\010\000\255\002\011\000\255\002\
\\012\000\255\002\013\000\255\002\014\000\224\000\051\000\223\000\
\\091\000\255\002\000\000\
\\001\000\006\000\000\003\008\000\000\003\010\000\000\003\011\000\000\003\
\\012\000\000\003\013\000\000\003\091\000\000\003\000\000\
\\001\000\006\000\001\003\008\000\001\003\010\000\001\003\011\000\001\003\
\\012\000\001\003\013\000\001\003\014\000\001\003\051\000\001\003\
\\052\000\225\000\091\000\001\003\000\000\
\\001\000\006\000\002\003\008\000\002\003\010\000\002\003\011\000\002\003\
\\012\000\002\003\013\000\002\003\014\000\002\003\051\000\002\003\
\\052\000\225\000\091\000\002\003\000\000\
\\001\000\006\000\003\003\008\000\003\003\010\000\003\003\011\000\003\003\
\\012\000\003\003\013\000\003\003\014\000\003\003\051\000\003\003\
\\052\000\003\003\053\000\222\000\091\000\003\003\000\000\
\\001\000\006\000\004\003\008\000\004\003\010\000\004\003\011\000\004\003\
\\012\000\004\003\013\000\004\003\014\000\004\003\051\000\004\003\
\\052\000\004\003\053\000\222\000\091\000\004\003\000\000\
\\001\000\006\000\005\003\008\000\005\003\010\000\005\003\011\000\005\003\
\\012\000\005\003\013\000\005\003\014\000\005\003\051\000\005\003\
\\052\000\005\003\053\000\005\003\054\000\221\000\091\000\005\003\000\000\
\\001\000\006\000\006\003\008\000\006\003\010\000\006\003\011\000\006\003\
\\012\000\006\003\013\000\006\003\014\000\006\003\051\000\006\003\
\\052\000\006\003\053\000\006\003\054\000\221\000\091\000\006\003\000\000\
\\001\000\006\000\007\003\008\000\007\003\010\000\007\003\011\000\007\003\
\\012\000\007\003\013\000\007\003\014\000\007\003\021\000\220\000\
\\051\000\007\003\052\000\007\003\053\000\007\003\054\000\007\003\
\\091\000\007\003\000\000\
\\001\000\006\000\008\003\008\000\008\003\010\000\008\003\011\000\008\003\
\\012\000\008\003\013\000\008\003\014\000\008\003\021\000\220\000\
\\051\000\008\003\052\000\008\003\053\000\008\003\054\000\008\003\
\\091\000\008\003\000\000\
\\001\000\006\000\009\003\008\000\009\003\010\000\009\003\011\000\009\003\
\\012\000\009\003\013\000\009\003\014\000\009\003\021\000\009\003\
\\051\000\009\003\052\000\009\003\053\000\009\003\054\000\009\003\
\\055\000\219\000\056\000\218\000\091\000\009\003\000\000\
\\001\000\006\000\010\003\008\000\010\003\010\000\010\003\011\000\010\003\
\\012\000\010\003\013\000\010\003\014\000\010\003\021\000\010\003\
\\051\000\010\003\052\000\010\003\053\000\010\003\054\000\010\003\
\\055\000\219\000\056\000\218\000\091\000\010\003\000\000\
\\001\000\006\000\011\003\008\000\011\003\010\000\011\003\011\000\011\003\
\\012\000\011\003\013\000\011\003\014\000\011\003\021\000\011\003\
\\051\000\011\003\052\000\011\003\053\000\011\003\054\000\011\003\
\\055\000\011\003\056\000\011\003\057\000\217\000\058\000\216\000\
\\059\000\215\000\060\000\214\000\091\000\011\003\000\000\
\\001\000\006\000\012\003\008\000\012\003\010\000\012\003\011\000\012\003\
\\012\000\012\003\013\000\012\003\014\000\012\003\021\000\012\003\
\\051\000\012\003\052\000\012\003\053\000\012\003\054\000\012\003\
\\055\000\012\003\056\000\012\003\057\000\217\000\058\000\216\000\
\\059\000\215\000\060\000\214\000\091\000\012\003\000\000\
\\001\000\006\000\013\003\008\000\013\003\010\000\013\003\011\000\013\003\
\\012\000\013\003\013\000\013\003\014\000\013\003\021\000\013\003\
\\051\000\013\003\052\000\013\003\053\000\013\003\054\000\013\003\
\\055\000\013\003\056\000\013\003\057\000\217\000\058\000\216\000\
\\059\000\215\000\060\000\214\000\091\000\013\003\000\000\
\\001\000\006\000\014\003\008\000\014\003\010\000\014\003\011\000\014\003\
\\012\000\014\003\013\000\014\003\014\000\014\003\021\000\014\003\
\\051\000\014\003\052\000\014\003\053\000\014\003\054\000\014\003\
\\055\000\014\003\056\000\014\003\057\000\014\003\058\000\014\003\
\\059\000\014\003\060\000\014\003\061\000\211\000\062\000\210\000\
\\091\000\014\003\000\000\
\\001\000\006\000\015\003\008\000\015\003\010\000\015\003\011\000\015\003\
\\012\000\015\003\013\000\015\003\014\000\015\003\021\000\015\003\
\\051\000\015\003\052\000\015\003\053\000\015\003\054\000\015\003\
\\055\000\015\003\056\000\015\003\057\000\015\003\058\000\015\003\
\\059\000\015\003\060\000\015\003\061\000\211\000\062\000\210\000\
\\091\000\015\003\000\000\
\\001\000\006\000\016\003\008\000\016\003\010\000\016\003\011\000\016\003\
\\012\000\016\003\013\000\016\003\014\000\016\003\021\000\016\003\
\\051\000\016\003\052\000\016\003\053\000\016\003\054\000\016\003\
\\055\000\016\003\056\000\016\003\057\000\016\003\058\000\016\003\
\\059\000\016\003\060\000\016\003\061\000\211\000\062\000\210\000\
\\091\000\016\003\000\000\
\\001\000\006\000\017\003\008\000\017\003\010\000\017\003\011\000\017\003\
\\012\000\017\003\013\000\017\003\014\000\017\003\021\000\017\003\
\\051\000\017\003\052\000\017\003\053\000\017\003\054\000\017\003\
\\055\000\017\003\056\000\017\003\057\000\017\003\058\000\017\003\
\\059\000\017\003\060\000\017\003\061\000\211\000\062\000\210\000\
\\091\000\017\003\000\000\
\\001\000\006\000\018\003\008\000\018\003\010\000\018\003\011\000\018\003\
\\012\000\018\003\013\000\018\003\014\000\018\003\021\000\018\003\
\\051\000\018\003\052\000\018\003\053\000\018\003\054\000\018\003\
\\055\000\018\003\056\000\018\003\057\000\018\003\058\000\018\003\
\\059\000\018\003\060\000\018\003\061\000\211\000\062\000\210\000\
\\091\000\018\003\000\000\
\\001\000\006\000\019\003\008\000\019\003\010\000\019\003\011\000\019\003\
\\012\000\019\003\013\000\019\003\014\000\019\003\017\000\213\000\
\\018\000\212\000\021\000\019\003\051\000\019\003\052\000\019\003\
\\053\000\019\003\054\000\019\003\055\000\019\003\056\000\019\003\
\\057\000\019\003\058\000\019\003\059\000\019\003\060\000\019\003\
\\061\000\019\003\062\000\019\003\091\000\019\003\000\000\
\\001\000\006\000\020\003\008\000\020\003\010\000\020\003\011\000\020\003\
\\012\000\020\003\013\000\020\003\014\000\020\003\017\000\213\000\
\\018\000\212\000\021\000\020\003\051\000\020\003\052\000\020\003\
\\053\000\020\003\054\000\020\003\055\000\020\003\056\000\020\003\
\\057\000\020\003\058\000\020\003\059\000\020\003\060\000\020\003\
\\061\000\020\003\062\000\020\003\091\000\020\003\000\000\
\\001\000\006\000\021\003\008\000\021\003\010\000\021\003\011\000\021\003\
\\012\000\021\003\013\000\021\003\014\000\021\003\017\000\213\000\
\\018\000\212\000\021\000\021\003\051\000\021\003\052\000\021\003\
\\053\000\021\003\054\000\021\003\055\000\021\003\056\000\021\003\
\\057\000\021\003\058\000\021\003\059\000\021\003\060\000\021\003\
\\061\000\021\003\062\000\021\003\091\000\021\003\000\000\
\\001\000\006\000\040\003\016\000\040\003\000\000\
\\001\000\006\000\041\003\016\000\041\003\000\000\
\\001\000\006\000\183\000\000\000\
\\001\000\006\000\226\000\000\000\
\\001\000\006\000\244\000\000\000\
\\001\000\006\000\041\001\000\000\
\\001\000\006\000\080\001\000\000\
\\001\000\006\000\081\001\000\000\
\\001\000\006\000\090\001\099\000\202\000\000\000\
\\001\000\006\000\132\001\000\000\
\\001\000\006\000\142\001\000\000\
\\001\000\006\000\146\001\000\000\
\\001\000\006\000\154\001\000\000\
\\001\000\006\000\155\001\000\000\
\\001\000\006\000\164\001\000\000\
\\001\000\006\000\174\001\000\000\
\\001\000\006\000\175\001\000\000\
\\001\000\006\000\176\001\000\000\
\\001\000\006\000\185\001\000\000\
\\001\000\006\000\188\001\000\000\
\\001\000\006\000\195\001\000\000\
\\001\000\006\000\201\001\016\000\200\001\000\000\
\\001\000\006\000\241\001\000\000\
\\001\000\006\000\242\001\000\000\
\\001\000\006\000\001\002\000\000\
\\001\000\006\000\011\002\000\000\
\\001\000\007\000\077\000\073\000\076\000\074\000\075\000\000\000\
\\001\000\007\000\079\000\073\000\076\000\074\000\075\000\000\000\
\\001\000\007\000\082\000\073\000\076\000\074\000\075\000\000\000\
\\001\000\007\000\092\000\011\000\097\002\012\000\097\002\015\000\091\000\000\000\
\\001\000\007\000\148\001\000\000\
\\001\000\007\000\191\001\000\000\
\\001\000\008\000\072\002\046\000\072\002\047\000\072\002\000\000\
\\001\000\008\000\079\002\035\000\047\000\049\000\046\000\063\000\045\000\
\\064\000\044\000\065\000\043\000\066\000\042\000\067\000\041\000\
\\068\000\040\000\069\000\039\000\070\000\038\000\071\000\037\000\
\\074\000\036\000\076\000\035\000\077\000\034\000\080\000\031\000\
\\081\000\030\000\082\000\029\000\000\000\
\\001\000\008\000\080\002\000\000\
\\001\000\008\000\090\002\035\000\090\002\049\000\090\002\063\000\090\002\
\\064\000\090\002\065\000\090\002\066\000\090\002\067\000\090\002\
\\068\000\090\002\069\000\090\002\070\000\090\002\071\000\090\002\
\\074\000\090\002\076\000\090\002\077\000\090\002\080\000\090\002\
\\081\000\090\002\082\000\090\002\000\000\
\\001\000\008\000\146\002\011\000\146\002\000\000\
\\001\000\008\000\147\002\011\000\147\002\000\000\
\\001\000\008\000\148\002\011\000\148\002\015\000\241\000\000\000\
\\001\000\008\000\149\002\011\000\149\002\000\000\
\\001\000\008\000\161\002\011\000\104\001\000\000\
\\001\000\008\000\163\002\000\000\
\\001\000\008\000\164\002\011\000\164\002\000\000\
\\001\000\008\000\165\002\011\000\165\002\000\000\
\\001\000\008\000\171\002\011\000\171\002\012\000\171\002\000\000\
\\001\000\008\000\172\002\011\000\172\002\012\000\172\002\000\000\
\\001\000\008\000\227\002\046\000\215\001\047\000\214\001\000\000\
\\001\000\008\000\228\002\000\000\
\\001\000\008\000\229\002\046\000\229\002\047\000\229\002\000\000\
\\001\000\008\000\195\000\000\000\
\\001\000\008\000\201\000\000\000\
\\001\000\008\000\240\000\011\000\239\000\000\000\
\\001\000\008\000\021\001\000\000\
\\001\000\008\000\046\001\000\000\
\\001\000\008\000\051\001\000\000\
\\001\000\008\000\086\001\011\000\085\001\000\000\
\\001\000\008\000\088\001\073\000\143\000\000\000\
\\001\000\008\000\105\001\000\000\
\\001\000\008\000\149\001\073\000\143\000\000\000\
\\001\000\008\000\202\001\000\000\
\\001\000\008\000\233\001\000\000\
\\001\000\009\000\169\002\015\000\169\002\016\000\169\002\000\000\
\\001\000\009\000\170\002\015\000\170\002\016\000\170\002\000\000\
\\001\000\009\000\069\000\073\000\068\000\089\000\049\002\090\000\049\002\
\\093\000\049\002\098\000\049\002\100\000\049\002\000\000\
\\001\000\009\000\069\000\073\000\068\000\100\000\049\002\000\000\
\\001\000\009\000\003\001\015\000\167\002\016\000\002\001\000\000\
\\001\000\009\000\207\001\099\000\129\000\000\000\
\\001\000\010\000\190\000\000\000\
\\001\000\010\000\243\000\000\000\
\\001\000\010\000\141\001\000\000\
\\001\000\010\000\153\001\000\000\
\\001\000\010\000\157\001\000\000\
\\001\000\010\000\184\001\000\000\
\\001\000\010\000\247\001\000\000\
\\001\000\011\000\093\002\012\000\093\002\013\000\050\001\000\000\
\\001\000\011\000\094\002\012\000\094\002\000\000\
\\001\000\011\000\097\002\012\000\097\002\015\000\091\000\000\000\
\\001\000\011\000\098\002\012\000\098\002\000\000\
\\001\000\011\000\240\002\012\000\240\002\000\000\
\\001\000\011\000\089\000\012\000\095\002\000\000\
\\001\000\011\000\049\001\012\000\091\002\000\000\
\\001\000\011\000\145\001\000\000\
\\001\000\011\000\166\001\012\000\238\002\000\000\
\\001\000\012\000\092\002\000\000\
\\001\000\012\000\096\002\000\000\
\\001\000\012\000\184\002\000\000\
\\001\000\012\000\237\002\000\000\
\\001\000\012\000\239\002\000\000\
\\001\000\012\000\242\002\000\000\
\\001\000\012\000\048\000\035\000\047\000\049\000\046\000\063\000\045\000\
\\064\000\044\000\065\000\043\000\066\000\042\000\067\000\041\000\
\\068\000\040\000\069\000\039\000\070\000\038\000\071\000\037\000\
\\074\000\036\000\076\000\035\000\077\000\034\000\078\000\033\000\
\\079\000\032\000\080\000\031\000\081\000\030\000\082\000\029\000\
\\084\000\028\000\085\000\027\000\086\000\026\000\087\000\025\000\
\\088\000\024\000\089\000\023\000\090\000\022\000\093\000\021\000\
\\095\000\020\000\098\000\019\000\101\000\018\000\103\000\017\000\000\000\
\\001\000\012\000\088\000\000\000\
\\001\000\012\000\004\001\000\000\
\\001\000\012\000\031\001\000\000\
\\001\000\012\000\032\001\000\000\
\\001\000\012\000\048\001\000\000\
\\001\000\012\000\109\001\000\000\
\\001\000\012\000\110\001\000\000\
\\001\000\012\000\126\001\000\000\
\\001\000\012\000\127\001\000\000\
\\001\000\012\000\158\001\000\000\
\\001\000\012\000\167\001\000\000\
\\001\000\012\000\194\001\000\000\
\\001\000\012\000\208\001\000\000\
\\001\000\012\000\254\001\000\000\
\\001\000\013\000\103\000\000\000\
\\001\000\013\000\019\001\000\000\
\\001\000\013\000\144\001\000\000\
\\001\000\013\000\234\001\000\000\
\\001\000\013\000\249\001\000\000\
\\001\000\015\000\168\002\000\000\
\\001\000\015\000\056\003\023\000\056\003\024\000\056\003\025\000\056\003\
\\026\000\056\003\027\000\056\003\028\000\056\003\029\000\056\003\
\\030\000\056\003\031\000\056\003\032\000\056\003\033\000\056\003\
\\034\000\056\003\000\000\
\\001\000\015\000\018\001\023\000\017\001\024\000\016\001\025\000\015\001\
\\026\000\014\001\027\000\013\001\028\000\012\001\029\000\011\001\
\\030\000\010\001\031\000\009\001\032\000\008\001\033\000\007\001\
\\034\000\006\001\000\000\
\\001\000\015\000\018\001\023\000\238\001\024\000\237\001\025\000\015\001\
\\026\000\014\001\027\000\013\001\028\000\012\001\029\000\011\001\
\\030\000\010\001\031\000\009\001\032\000\008\001\033\000\007\001\
\\034\000\006\001\000\000\
\\001\000\015\000\102\001\000\000\
\\001\000\015\000\165\001\000\000\
\\001\000\035\000\047\000\049\000\046\000\063\000\045\000\064\000\044\000\
\\065\000\043\000\066\000\042\000\067\000\041\000\068\000\040\000\
\\069\000\039\000\070\000\038\000\071\000\037\000\074\000\036\000\
\\076\000\035\000\077\000\034\000\000\000\
\\001\000\035\000\047\000\049\000\046\000\063\000\045\000\064\000\044\000\
\\065\000\043\000\066\000\042\000\067\000\041\000\068\000\040\000\
\\069\000\039\000\070\000\038\000\071\000\037\000\074\000\036\000\
\\076\000\035\000\077\000\034\000\078\000\033\000\079\000\032\000\
\\080\000\031\000\081\000\030\000\082\000\029\000\084\000\028\000\
\\085\000\027\000\086\000\026\000\087\000\025\000\088\000\024\000\
\\089\000\023\000\090\000\022\000\093\000\021\000\095\000\020\000\
\\098\000\019\000\101\000\018\000\103\000\017\000\000\000\
\\001\000\035\000\047\000\049\000\046\000\063\000\045\000\064\000\044\000\
\\065\000\043\000\066\000\042\000\067\000\041\000\068\000\040\000\
\\069\000\039\000\070\000\038\000\071\000\037\000\074\000\036\000\
\\076\000\035\000\077\000\034\000\080\000\031\000\081\000\030\000\
\\082\000\029\000\000\000\
\\001\000\038\000\172\001\000\000\
\\001\000\073\000\066\000\000\000\
\\001\000\073\000\073\000\000\000\
\\001\000\073\000\073\000\089\000\046\002\090\000\046\002\093\000\046\002\
\\098\000\046\002\100\000\046\002\000\000\
\\001\000\073\000\143\000\000\000\
\\001\000\073\000\030\001\000\000\
\\001\000\073\000\053\001\000\000\
\\001\000\073\000\054\001\000\000\
\\001\000\073\000\106\001\000\000\
\\001\000\073\000\181\001\000\000\
\\001\000\073\000\223\001\000\000\
\\001\000\073\000\228\001\000\000\
\\001\000\089\000\042\002\090\000\042\002\093\000\042\002\098\000\042\002\
\\100\000\042\002\000\000\
\\001\000\089\000\043\002\090\000\043\002\093\000\043\002\098\000\043\002\
\\100\000\043\002\000\000\
\\001\000\089\000\044\002\090\000\044\002\093\000\044\002\098\000\044\002\
\\100\000\044\002\000\000\
\\001\000\089\000\045\002\090\000\045\002\093\000\045\002\098\000\045\002\
\\100\000\045\002\000\000\
\\001\000\089\000\047\002\090\000\047\002\093\000\047\002\098\000\047\002\
\\100\000\047\002\000\000\
\\001\000\089\000\048\002\090\000\048\002\093\000\048\002\098\000\048\002\
\\100\000\048\002\000\000\
\\001\000\089\000\050\002\090\000\050\002\093\000\050\002\098\000\050\002\
\\100\000\050\002\000\000\
\\001\000\089\000\051\002\090\000\051\002\093\000\051\002\098\000\051\002\
\\100\000\051\002\000\000\
\\001\000\089\000\023\000\090\000\022\000\093\000\021\000\098\000\019\000\
\\100\000\040\002\000\000\
\\001\000\097\000\076\002\000\000\
\\001\000\097\000\078\002\000\000\
\\001\000\097\000\189\001\000\000\
\\001\000\099\000\071\000\000\000\
\\001\000\099\000\129\000\000\000\
\\001\000\099\000\191\000\000\000\
\\001\000\099\000\024\001\000\000\
\\001\000\099\000\025\001\000\000\
\\001\000\099\000\026\001\000\000\
\\001\000\099\000\129\001\000\000\
\\001\000\099\000\209\001\000\000\
\\001\000\099\000\251\001\000\000\
\\001\000\100\000\041\002\000\000\
\\001\000\100\000\059\000\000\000\
\\001\000\100\000\100\000\000\000\
\\001\000\100\000\113\001\000\000\
\\001\000\100\000\114\001\000\000\
\\001\000\100\000\115\001\000\000\
\\001\000\100\000\173\001\000\000\
\\001\000\100\000\183\001\000\000\
\\001\000\100\000\229\001\000\000\
\\001\000\100\000\003\002\000\000\
\"
val actionRowNumbers =
"\119\001\020\000\064\000\025\000\
\\004\000\005\000\148\000\182\001\
\\168\001\029\000\027\000\065\000\
\\023\000\002\000\001\000\014\000\
\\201\000\163\001\149\001\093\001\
\\172\001\150\001\015\000\016\000\
\\018\000\013\000\017\000\039\000\
\\038\000\037\000\012\000\011\000\
\\056\001\057\001\066\000\059\000\
\\061\000\060\000\056\000\058\000\
\\057\000\055\000\062\000\054\000\
\\202\000\058\001\006\000\026\000\
\\205\000\120\001\109\001\059\001\
\\200\000\183\000\007\000\149\000\
\\146\000\019\000\181\001\030\000\
\\028\000\024\000\003\000\206\000\
\\183\001\160\001\093\001\154\000\
\\162\001\165\001\161\001\134\001\
\\049\000\043\000\042\000\147\001\
\\044\000\147\001\166\000\071\000\
\\152\001\188\000\189\000\207\000\
\\161\000\231\000\008\000\149\000\
\\009\000\159\000\169\000\199\000\
\\203\000\032\001\179\000\147\000\
\\040\000\223\000\022\000\166\001\
\\097\001\174\001\147\001\033\000\
\\063\001\079\001\149\000\035\000\
\\147\001\080\001\142\000\140\000\
\\132\000\121\000\115\000\119\000\
\\173\000\022\001\027\001\019\001\
\\017\001\015\001\013\001\011\001\
\\007\001\009\001\033\001\144\000\
\\145\000\138\000\209\000\167\000\
\\166\000\166\000\166\000\166\000\
\\165\000\166\000\152\001\066\001\
\\081\001\068\001\173\001\098\001\
\\185\000\232\000\034\001\233\000\
\\151\000\114\001\106\001\074\001\
\\107\001\158\000\122\000\121\001\
\\141\001\135\001\032\000\100\000\
\\168\000\082\001\031\000\148\000\
\\197\000\175\001\176\001\177\001\
\\139\000\211\000\212\000\153\001\
\\122\001\123\001\164\000\107\000\
\\213\000\214\000\096\000\166\000\
\\204\000\186\000\180\000\041\000\
\\035\001\224\000\226\000\215\000\
\\093\001\151\001\083\001\034\000\
\\064\001\052\000\124\001\110\001\
\\104\001\036\000\084\001\047\000\
\\143\000\154\001\155\001\166\000\
\\155\000\166\000\166\000\166\000\
\\166\000\166\000\166\000\166\000\
\\166\000\166\000\166\000\166\000\
\\166\000\166\000\166\000\166\000\
\\166\000\166\000\166\000\166\000\
\\063\000\145\001\129\000\165\000\
\\125\000\126\000\124\000\123\000\
\\036\001\037\001\153\000\127\000\
\\085\001\086\001\067\000\166\000\
\\038\001\184\000\182\000\146\001\
\\218\000\236\000\235\000\210\000\
\\162\000\150\000\095\001\143\001\
\\159\000\073\001\070\001\087\001\
\\156\001\166\000\085\000\166\000\
\\083\000\082\000\078\000\081\000\
\\080\000\079\000\076\000\077\000\
\\075\000\074\000\125\001\126\001\
\\073\000\172\000\062\001\010\000\
\\219\000\198\000\184\001\185\001\
\\186\001\166\000\177\000\127\001\
\\115\001\092\000\091\000\128\001\
\\090\000\172\000\108\000\178\001\
\\166\000\166\000\128\000\039\001\
\\223\000\156\000\167\001\164\001\
\\050\000\053\000\065\001\149\000\
\\166\000\045\000\048\000\136\000\
\\135\000\099\001\040\001\004\001\
\\005\001\118\000\117\000\116\000\
\\029\001\028\001\175\000\174\000\
\\024\001\023\001\026\001\025\001\
\\021\001\020\001\018\001\016\001\
\\014\001\010\001\136\001\012\001\
\\111\001\041\001\141\000\160\000\
\\237\000\216\000\152\000\088\001\
\\068\000\067\001\069\000\069\001\
\\190\000\187\000\094\001\234\000\
\\166\000\231\000\217\000\100\001\
\\193\000\042\001\043\001\139\001\
\\072\000\072\001\157\000\075\001\
\\092\001\101\001\129\001\098\000\
\\097\000\101\000\173\001\170\000\
\\103\000\102\000\044\001\208\000\
\\144\001\112\001\116\001\130\001\
\\163\000\114\000\165\000\166\000\
\\093\000\089\000\148\001\187\001\
\\045\001\046\001\021\000\225\000\
\\047\001\229\000\227\000\051\000\
\\113\001\105\001\046\000\133\000\
\\134\000\166\000\166\000\157\001\
\\130\000\120\000\158\000\070\000\
\\188\001\102\001\048\001\192\000\
\\191\000\195\000\071\001\091\001\
\\084\000\239\000\049\001\169\001\
\\171\001\171\000\061\001\166\000\
\\178\000\113\000\118\001\131\001\
\\050\001\140\001\220\000\106\000\
\\107\000\172\000\228\000\166\000\
\\006\001\008\001\051\001\030\001\
\\089\001\181\000\194\000\196\000\
\\238\000\247\000\132\001\179\001\
\\170\001\076\001\108\001\117\001\
\\176\000\060\001\166\000\172\000\
\\094\000\230\000\158\001\131\000\
\\137\000\248\000\241\000\249\000\
\\221\000\159\001\105\000\189\001\
\\109\000\172\000\076\001\090\001\
\\137\001\166\000\142\001\254\000\
\\253\000\052\001\053\001\086\000\
\\172\000\031\001\240\000\247\000\
\\096\001\166\000\103\001\104\000\
\\110\000\168\000\077\001\099\000\
\\112\000\138\001\166\000\003\001\
\\002\001\180\001\178\000\107\000\
\\133\001\095\000\243\000\250\000\
\\054\001\173\001\078\001\111\000\
\\001\001\190\001\000\001\172\000\
\\087\000\242\000\173\001\251\000\
\\222\000\255\000\088\000\244\000\
\\245\000\166\000\173\001\055\001\
\\246\000\252\000\000\000"
val gotoT =
"\
\\001\000\010\002\002\000\014\000\003\000\013\000\006\000\012\000\
\\007\000\011\000\010\000\010\000\012\000\009\000\013\000\008\000\
\\014\000\007\000\020\000\006\000\028\000\005\000\040\000\004\000\
\\069\000\003\000\070\000\002\000\094\000\001\000\000\000\
\\000\000\
\\000\000\
\\006\000\012\000\007\000\011\000\010\000\010\000\012\000\009\000\
\\013\000\008\000\014\000\007\000\020\000\047\000\069\000\003\000\
\\070\000\002\000\094\000\001\000\000\000\
\\000\000\
\\000\000\
\\059\000\052\000\060\000\051\000\065\000\050\000\066\000\049\000\
\\067\000\048\000\000\000\
\\000\000\
\\013\000\008\000\014\000\058\000\000\000\
\\006\000\012\000\007\000\011\000\010\000\010\000\012\000\009\000\
\\013\000\008\000\014\000\007\000\020\000\059\000\069\000\003\000\
\\070\000\002\000\094\000\001\000\000\000\
\\006\000\012\000\007\000\011\000\010\000\010\000\012\000\009\000\
\\013\000\008\000\014\000\007\000\020\000\060\000\069\000\003\000\
\\070\000\002\000\094\000\001\000\000\000\
\\000\000\
\\006\000\012\000\007\000\011\000\010\000\010\000\012\000\009\000\
\\013\000\008\000\014\000\007\000\020\000\061\000\069\000\003\000\
\\070\000\002\000\094\000\001\000\000\000\
\\002\000\062\000\003\000\013\000\006\000\012\000\007\000\011\000\
\\010\000\010\000\012\000\009\000\013\000\008\000\014\000\007\000\
\\020\000\006\000\028\000\005\000\040\000\004\000\069\000\003\000\
\\070\000\002\000\094\000\001\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\091\000\065\000\000\000\
\\016\000\068\000\000\000\
\\015\000\070\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\071\000\072\000\000\000\
\\071\000\076\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\071\000\079\000\000\000\
\\000\000\
\\000\000\
\\068\000\082\000\094\000\081\000\000\000\
\\000\000\
\\000\000\
\\041\000\088\000\000\000\
\\067\000\092\000\094\000\091\000\000\000\
\\000\000\
\\000\000\
\\059\000\052\000\060\000\093\000\067\000\048\000\000\000\
\\010\000\096\000\011\000\095\000\059\000\094\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\091\000\099\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\007\000\011\000\010\000\107\000\021\000\106\000\029\000\105\000\
\\030\000\104\000\069\000\103\000\070\000\002\000\000\000\
\\000\000\
\\007\000\011\000\010\000\107\000\021\000\106\000\029\000\109\000\
\\030\000\104\000\069\000\103\000\070\000\002\000\000\000\
\\073\000\126\000\076\000\125\000\077\000\124\000\078\000\123\000\
\\079\000\122\000\080\000\121\000\081\000\120\000\082\000\119\000\
\\083\000\118\000\084\000\117\000\085\000\116\000\086\000\115\000\
\\087\000\114\000\088\000\113\000\089\000\112\000\090\000\111\000\
\\101\000\110\000\000\000\
\\000\000\
\\008\000\140\000\009\000\139\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\073\000\143\000\076\000\125\000\077\000\124\000\078\000\123\000\
\\079\000\122\000\080\000\121\000\081\000\120\000\082\000\119\000\
\\083\000\118\000\084\000\117\000\085\000\116\000\086\000\115\000\
\\087\000\114\000\088\000\113\000\089\000\112\000\090\000\111\000\
\\101\000\110\000\000\000\
\\006\000\012\000\007\000\011\000\010\000\010\000\012\000\009\000\
\\013\000\008\000\014\000\007\000\020\000\148\000\037\000\147\000\
\\038\000\146\000\039\000\145\000\069\000\003\000\070\000\002\000\
\\094\000\001\000\000\000\
\\000\000\
\\059\000\052\000\060\000\150\000\065\000\050\000\066\000\149\000\
\\067\000\048\000\000\000\
\\000\000\
\\024\000\152\000\073\000\151\000\076\000\125\000\077\000\124\000\
\\078\000\123\000\079\000\122\000\080\000\121\000\081\000\120\000\
\\082\000\119\000\083\000\118\000\084\000\117\000\085\000\116\000\
\\086\000\115\000\087\000\114\000\088\000\113\000\089\000\112\000\
\\090\000\111\000\101\000\110\000\000\000\
\\006\000\012\000\007\000\011\000\010\000\010\000\012\000\009\000\
\\013\000\008\000\014\000\007\000\020\000\163\000\028\000\162\000\
\\035\000\161\000\036\000\160\000\041\000\159\000\042\000\158\000\
\\045\000\157\000\069\000\003\000\070\000\002\000\072\000\156\000\
\\073\000\155\000\076\000\125\000\077\000\124\000\078\000\123\000\
\\079\000\122\000\080\000\121\000\081\000\120\000\082\000\119\000\
\\083\000\118\000\084\000\117\000\085\000\116\000\086\000\115\000\
\\087\000\114\000\088\000\154\000\089\000\112\000\090\000\111\000\
\\094\000\001\000\101\000\110\000\000\000\
\\067\000\180\000\000\000\
\\068\000\082\000\094\000\081\000\000\000\
\\000\000\
\\000\000\
\\059\000\182\000\000\000\
\\010\000\096\000\011\000\183\000\000\000\
\\093\000\185\000\095\000\184\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\007\000\011\000\010\000\107\000\021\000\106\000\029\000\190\000\
\\030\000\104\000\069\000\103\000\070\000\002\000\000\000\
\\007\000\011\000\010\000\107\000\021\000\191\000\069\000\103\000\
\\070\000\002\000\000\000\
\\007\000\011\000\010\000\107\000\021\000\106\000\029\000\192\000\
\\030\000\104\000\069\000\103\000\070\000\002\000\000\000\
\\000\000\
\\059\000\052\000\060\000\196\000\063\000\195\000\064\000\194\000\
\\067\000\048\000\000\000\
\\007\000\011\000\010\000\107\000\021\000\197\000\069\000\103\000\
\\070\000\002\000\000\000\
\\007\000\011\000\010\000\107\000\021\000\106\000\029\000\198\000\
\\030\000\104\000\069\000\103\000\070\000\002\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\086\000\226\000\088\000\113\000\089\000\112\000\090\000\111\000\
\\101\000\110\000\000\000\
\\086\000\115\000\087\000\228\000\088\000\113\000\089\000\112\000\
\\090\000\111\000\101\000\110\000\000\000\
\\086\000\115\000\087\000\229\000\088\000\113\000\089\000\112\000\
\\090\000\111\000\101\000\110\000\000\000\
\\086\000\115\000\087\000\230\000\088\000\113\000\089\000\112\000\
\\090\000\111\000\101\000\110\000\000\000\
\\086\000\115\000\087\000\231\000\088\000\113\000\089\000\112\000\
\\090\000\111\000\101\000\110\000\000\000\
\\007\000\011\000\010\000\107\000\021\000\234\000\034\000\233\000\
\\069\000\103\000\070\000\002\000\073\000\232\000\076\000\125\000\
\\077\000\124\000\078\000\123\000\079\000\122\000\080\000\121\000\
\\081\000\120\000\082\000\119\000\083\000\118\000\084\000\117\000\
\\085\000\116\000\086\000\115\000\087\000\114\000\088\000\113\000\
\\089\000\112\000\090\000\111\000\101\000\110\000\000\000\
\\086\000\115\000\087\000\235\000\088\000\113\000\089\000\112\000\
\\090\000\111\000\101\000\110\000\000\000\
\\008\000\236\000\009\000\139\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\101\000\240\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\059\000\247\000\060\000\246\000\061\000\245\000\062\000\244\000\
\\067\000\048\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\022\000\255\000\023\000\254\000\024\000\253\000\025\000\252\000\
\\026\000\251\000\027\000\250\000\073\000\151\000\076\000\125\000\
\\077\000\124\000\078\000\123\000\079\000\122\000\080\000\121\000\
\\081\000\120\000\082\000\119\000\083\000\118\000\084\000\117\000\
\\085\000\116\000\086\000\115\000\087\000\114\000\088\000\113\000\
\\089\000\112\000\090\000\111\000\101\000\110\000\000\000\
\\000\000\
\\000\000\
\\058\000\003\001\000\000\
\\000\000\
\\000\000\
\\000\000\
\\006\000\012\000\007\000\011\000\010\000\010\000\012\000\009\000\
\\013\000\008\000\014\000\007\000\020\000\163\000\028\000\162\000\
\\035\000\018\001\036\000\160\000\041\000\159\000\042\000\158\000\
\\045\000\157\000\069\000\003\000\070\000\002\000\072\000\156\000\
\\073\000\155\000\076\000\125\000\077\000\124\000\078\000\123\000\
\\079\000\122\000\080\000\121\000\081\000\120\000\082\000\119\000\
\\083\000\118\000\084\000\117\000\085\000\116\000\086\000\115\000\
\\087\000\114\000\088\000\154\000\089\000\112\000\090\000\111\000\
\\094\000\001\000\101\000\110\000\000\000\
\\000\000\
\\000\000\
\\059\000\052\000\060\000\150\000\065\000\050\000\066\000\049\000\
\\067\000\048\000\000\000\
\\005\000\020\001\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\045\000\027\001\000\000\
\\000\000\
\\000\000\
\\073\000\031\001\076\000\125\000\077\000\124\000\078\000\123\000\
\\079\000\122\000\080\000\121\000\081\000\120\000\082\000\119\000\
\\083\000\118\000\084\000\117\000\085\000\116\000\086\000\115\000\
\\087\000\114\000\088\000\113\000\089\000\112\000\090\000\111\000\
\\101\000\110\000\000\000\
\\018\000\034\001\019\000\033\001\000\000\
\\000\000\
\\000\000\
\\000\000\
\\086\000\115\000\087\000\038\001\088\000\113\000\089\000\112\000\
\\090\000\111\000\101\000\110\000\000\000\
\\068\000\082\000\094\000\081\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\091\000\042\001\000\000\
\\015\000\043\001\000\000\
\\000\000\
\\000\000\
\\000\000\
\\094\000\045\001\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\094\000\050\001\000\000\
\\000\000\
\\000\000\
\\000\000\
\\073\000\053\001\076\000\125\000\077\000\124\000\078\000\123\000\
\\079\000\122\000\080\000\121\000\081\000\120\000\082\000\119\000\
\\083\000\118\000\084\000\117\000\085\000\116\000\086\000\115\000\
\\087\000\114\000\088\000\113\000\089\000\112\000\090\000\111\000\
\\101\000\110\000\000\000\
\\073\000\056\001\074\000\055\001\075\000\054\001\076\000\125\000\
\\077\000\124\000\078\000\123\000\079\000\122\000\080\000\121\000\
\\081\000\120\000\082\000\119\000\083\000\118\000\084\000\117\000\
\\085\000\116\000\086\000\115\000\087\000\114\000\088\000\113\000\
\\089\000\112\000\090\000\111\000\101\000\110\000\000\000\
\\086\000\115\000\087\000\057\001\088\000\113\000\089\000\112\000\
\\090\000\111\000\101\000\110\000\000\000\
\\086\000\115\000\087\000\058\001\088\000\113\000\089\000\112\000\
\\090\000\111\000\101\000\110\000\000\000\
\\086\000\115\000\087\000\059\001\088\000\113\000\089\000\112\000\
\\090\000\111\000\101\000\110\000\000\000\
\\083\000\060\001\085\000\116\000\086\000\115\000\087\000\114\000\
\\088\000\113\000\089\000\112\000\090\000\111\000\101\000\110\000\000\000\
\\083\000\061\001\085\000\116\000\086\000\115\000\087\000\114\000\
\\088\000\113\000\089\000\112\000\090\000\111\000\101\000\110\000\000\000\
\\085\000\062\001\086\000\115\000\087\000\114\000\088\000\113\000\
\\089\000\112\000\090\000\111\000\101\000\110\000\000\000\
\\085\000\063\001\086\000\115\000\087\000\114\000\088\000\113\000\
\\089\000\112\000\090\000\111\000\101\000\110\000\000\000\
\\083\000\118\000\084\000\064\001\085\000\116\000\086\000\115\000\
\\087\000\114\000\088\000\113\000\089\000\112\000\090\000\111\000\
\\101\000\110\000\000\000\
\\083\000\118\000\084\000\065\001\085\000\116\000\086\000\115\000\
\\087\000\114\000\088\000\113\000\089\000\112\000\090\000\111\000\
\\101\000\110\000\000\000\
\\083\000\118\000\084\000\066\001\085\000\116\000\086\000\115\000\
\\087\000\114\000\088\000\113\000\089\000\112\000\090\000\111\000\
\\101\000\110\000\000\000\
\\083\000\118\000\084\000\067\001\085\000\116\000\086\000\115\000\
\\087\000\114\000\088\000\113\000\089\000\112\000\090\000\111\000\
\\101\000\110\000\000\000\
\\082\000\068\001\083\000\118\000\084\000\117\000\085\000\116\000\
\\086\000\115\000\087\000\114\000\088\000\113\000\089\000\112\000\
\\090\000\111\000\101\000\110\000\000\000\
\\082\000\069\001\083\000\118\000\084\000\117\000\085\000\116\000\
\\086\000\115\000\087\000\114\000\088\000\113\000\089\000\112\000\
\\090\000\111\000\101\000\110\000\000\000\
\\081\000\070\001\082\000\119\000\083\000\118\000\084\000\117\000\
\\085\000\116\000\086\000\115\000\087\000\114\000\088\000\113\000\
\\089\000\112\000\090\000\111\000\101\000\110\000\000\000\
\\080\000\071\001\081\000\120\000\082\000\119\000\083\000\118\000\
\\084\000\117\000\085\000\116\000\086\000\115\000\087\000\114\000\
\\088\000\113\000\089\000\112\000\090\000\111\000\101\000\110\000\000\000\
\\079\000\072\001\080\000\121\000\081\000\120\000\082\000\119\000\
\\083\000\118\000\084\000\117\000\085\000\116\000\086\000\115\000\
\\087\000\114\000\088\000\113\000\089\000\112\000\090\000\111\000\
\\101\000\110\000\000\000\
\\076\000\073\001\078\000\123\000\079\000\122\000\080\000\121\000\
\\081\000\120\000\082\000\119\000\083\000\118\000\084\000\117\000\
\\085\000\116\000\086\000\115\000\087\000\114\000\088\000\113\000\
\\089\000\112\000\090\000\111\000\101\000\110\000\000\000\
\\073\000\074\001\076\000\125\000\077\000\124\000\078\000\123\000\
\\079\000\122\000\080\000\121\000\081\000\120\000\082\000\119\000\
\\083\000\118\000\084\000\117\000\085\000\116\000\086\000\115\000\
\\087\000\114\000\088\000\113\000\089\000\112\000\090\000\111\000\
\\101\000\110\000\000\000\
\\078\000\075\001\079\000\122\000\080\000\121\000\081\000\120\000\
\\082\000\119\000\083\000\118\000\084\000\117\000\085\000\116\000\
\\086\000\115\000\087\000\114\000\088\000\113\000\089\000\112\000\
\\090\000\111\000\101\000\110\000\000\000\
\\000\000\
\\007\000\011\000\069\000\076\001\070\000\002\000\000\000\
\\000\000\
\\007\000\011\000\010\000\107\000\021\000\234\000\034\000\077\001\
\\069\000\103\000\070\000\002\000\073\000\232\000\076\000\125\000\
\\077\000\124\000\078\000\123\000\079\000\122\000\080\000\121\000\
\\081\000\120\000\082\000\119\000\083\000\118\000\084\000\117\000\
\\085\000\116\000\086\000\115\000\087\000\114\000\088\000\113\000\
\\089\000\112\000\090\000\111\000\101\000\110\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\059\000\081\001\061\000\080\001\062\000\244\000\000\000\
\\000\000\
\\000\000\
\\009\000\085\001\000\000\
\\000\000\
\\073\000\087\001\076\000\125\000\077\000\124\000\078\000\123\000\
\\079\000\122\000\080\000\121\000\081\000\120\000\082\000\119\000\
\\083\000\118\000\084\000\117\000\085\000\116\000\086\000\115\000\
\\087\000\114\000\088\000\113\000\089\000\112\000\090\000\111\000\
\\101\000\110\000\000\000\
\\000\000\
\\000\000\
\\106\000\089\001\000\000\
\\006\000\012\000\007\000\011\000\010\000\010\000\012\000\009\000\
\\013\000\008\000\014\000\007\000\020\000\148\000\037\000\147\000\
\\039\000\091\001\069\000\003\000\070\000\002\000\094\000\001\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\062\000\094\001\067\000\092\000\094\000\091\000\000\000\
\\073\000\095\001\076\000\125\000\077\000\124\000\078\000\123\000\
\\079\000\122\000\080\000\121\000\081\000\120\000\082\000\119\000\
\\083\000\118\000\084\000\117\000\085\000\116\000\086\000\115\000\
\\087\000\114\000\088\000\113\000\089\000\112\000\090\000\111\000\
\\101\000\110\000\000\000\
\\006\000\012\000\007\000\011\000\010\000\010\000\012\000\009\000\
\\013\000\008\000\014\000\007\000\020\000\148\000\037\000\147\000\
\\038\000\098\001\039\000\145\000\059\000\247\000\060\000\093\000\
\\061\000\097\001\062\000\244\000\067\000\048\000\069\000\003\000\
\\070\000\002\000\094\000\001\000\000\000\
\\026\000\099\001\027\000\250\000\000\000\
\\000\000\
\\024\000\101\001\073\000\151\000\076\000\125\000\077\000\124\000\
\\078\000\123\000\079\000\122\000\080\000\121\000\081\000\120\000\
\\082\000\119\000\083\000\118\000\084\000\117\000\085\000\116\000\
\\086\000\115\000\087\000\114\000\088\000\113\000\089\000\112\000\
\\090\000\111\000\101\000\110\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\073\000\105\001\076\000\125\000\077\000\124\000\078\000\123\000\
\\079\000\122\000\080\000\121\000\081\000\120\000\082\000\119\000\
\\083\000\118\000\084\000\117\000\085\000\116\000\086\000\115\000\
\\087\000\114\000\088\000\113\000\089\000\112\000\090\000\111\000\
\\101\000\110\000\000\000\
\\000\000\
\\073\000\106\001\076\000\125\000\077\000\124\000\078\000\123\000\
\\079\000\122\000\080\000\121\000\081\000\120\000\082\000\119\000\
\\083\000\118\000\084\000\117\000\085\000\116\000\086\000\115\000\
\\087\000\114\000\088\000\113\000\089\000\112\000\090\000\111\000\
\\101\000\110\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\041\000\159\000\042\000\109\001\045\000\157\000\072\000\156\000\
\\073\000\155\000\076\000\125\000\077\000\124\000\078\000\123\000\
\\079\000\122\000\080\000\121\000\081\000\120\000\082\000\119\000\
\\083\000\118\000\084\000\117\000\085\000\116\000\086\000\115\000\
\\087\000\114\000\088\000\154\000\089\000\112\000\090\000\111\000\
\\101\000\110\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\073\000\114\001\076\000\125\000\077\000\124\000\078\000\123\000\
\\079\000\122\000\080\000\121\000\081\000\120\000\082\000\119\000\
\\083\000\118\000\084\000\117\000\085\000\116\000\086\000\115\000\
\\087\000\114\000\088\000\113\000\089\000\112\000\090\000\111\000\
\\101\000\110\000\000\000\
\\006\000\012\000\007\000\011\000\010\000\010\000\012\000\009\000\
\\013\000\008\000\014\000\007\000\020\000\163\000\028\000\121\001\
\\050\000\120\001\051\000\119\001\052\000\118\001\053\000\117\001\
\\069\000\003\000\070\000\002\000\072\000\116\001\088\000\115\001\
\\089\000\112\000\090\000\111\000\094\000\001\000\101\000\110\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\041\000\159\000\042\000\126\001\045\000\157\000\072\000\156\000\
\\073\000\155\000\076\000\125\000\077\000\124\000\078\000\123\000\
\\079\000\122\000\080\000\121\000\081\000\120\000\082\000\119\000\
\\083\000\118\000\084\000\117\000\085\000\116\000\086\000\115\000\
\\087\000\114\000\088\000\154\000\089\000\112\000\090\000\111\000\
\\101\000\110\000\000\000\
\\000\000\
\\000\000\
\\073\000\128\001\076\000\125\000\077\000\124\000\078\000\123\000\
\\079\000\122\000\080\000\121\000\081\000\120\000\082\000\119\000\
\\083\000\118\000\084\000\117\000\085\000\116\000\086\000\115\000\
\\087\000\114\000\088\000\113\000\089\000\112\000\090\000\111\000\
\\101\000\110\000\000\000\
\\073\000\129\001\076\000\125\000\077\000\124\000\078\000\123\000\
\\079\000\122\000\080\000\121\000\081\000\120\000\082\000\119\000\
\\083\000\118\000\084\000\117\000\085\000\116\000\086\000\115\000\
\\087\000\114\000\088\000\113\000\089\000\112\000\090\000\111\000\
\\101\000\110\000\000\000\
\\000\000\
\\000\000\
\\093\000\185\000\095\000\131\001\000\000\
\\073\000\133\001\076\000\125\000\077\000\124\000\078\000\123\000\
\\079\000\122\000\080\000\121\000\081\000\120\000\082\000\119\000\
\\083\000\118\000\084\000\117\000\085\000\116\000\086\000\115\000\
\\087\000\114\000\088\000\113\000\089\000\112\000\090\000\111\000\
\\096\000\132\001\101\000\110\000\000\000\
\\000\000\
\\000\000\
\\094\000\135\001\000\000\
\\000\000\
\\000\000\
\\059\000\052\000\060\000\196\000\063\000\195\000\064\000\136\001\
\\067\000\048\000\000\000\
\\073\000\137\001\076\000\125\000\077\000\124\000\078\000\123\000\
\\079\000\122\000\080\000\121\000\081\000\120\000\082\000\119\000\
\\083\000\118\000\084\000\117\000\085\000\116\000\086\000\115\000\
\\087\000\114\000\088\000\113\000\089\000\112\000\090\000\111\000\
\\101\000\110\000\000\000\
\\094\000\138\001\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\086\000\115\000\087\000\145\001\088\000\113\000\089\000\112\000\
\\090\000\111\000\101\000\110\000\000\000\
\\000\000\
\\062\000\094\001\000\000\
\\006\000\012\000\007\000\011\000\010\000\010\000\012\000\009\000\
\\013\000\008\000\014\000\007\000\020\000\148\000\037\000\147\000\
\\038\000\098\001\039\000\145\000\059\000\081\001\061\000\097\001\
\\062\000\244\000\069\000\003\000\070\000\002\000\094\000\001\000\000\000\
\\009\000\085\001\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\091\000\148\001\000\000\
\\000\000\
\\073\000\149\001\076\000\125\000\077\000\124\000\078\000\123\000\
\\079\000\122\000\080\000\121\000\081\000\120\000\082\000\119\000\
\\083\000\118\000\084\000\117\000\085\000\116\000\086\000\115\000\
\\087\000\114\000\088\000\113\000\089\000\112\000\090\000\111\000\
\\101\000\110\000\000\000\
\\006\000\012\000\007\000\011\000\010\000\010\000\012\000\009\000\
\\013\000\008\000\014\000\007\000\020\000\148\000\037\000\147\000\
\\038\000\150\001\039\000\145\000\069\000\003\000\070\000\002\000\
\\094\000\001\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\022\000\154\001\023\000\254\000\024\000\253\000\025\000\252\000\
\\026\000\251\000\027\000\250\000\073\000\151\000\076\000\125\000\
\\077\000\124\000\078\000\123\000\079\000\122\000\080\000\121\000\
\\081\000\120\000\082\000\119\000\083\000\118\000\084\000\117\000\
\\085\000\116\000\086\000\115\000\087\000\114\000\088\000\113\000\
\\089\000\112\000\090\000\111\000\101\000\110\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\097\000\158\001\101\000\157\001\000\000\
\\041\000\159\000\042\000\161\001\043\000\160\001\044\000\159\001\
\\045\000\157\000\072\000\156\000\073\000\155\000\076\000\125\000\
\\077\000\124\000\078\000\123\000\079\000\122\000\080\000\121\000\
\\081\000\120\000\082\000\119\000\083\000\118\000\084\000\117\000\
\\085\000\116\000\086\000\115\000\087\000\114\000\088\000\154\000\
\\089\000\112\000\090\000\111\000\101\000\110\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\054\000\167\001\073\000\166\001\076\000\125\000\077\000\124\000\
\\078\000\123\000\079\000\122\000\080\000\121\000\081\000\120\000\
\\082\000\119\000\083\000\118\000\084\000\117\000\085\000\116\000\
\\086\000\115\000\087\000\114\000\088\000\113\000\089\000\112\000\
\\090\000\111\000\101\000\110\000\000\000\
\\000\000\
\\007\000\011\000\010\000\107\000\021\000\234\000\034\000\168\001\
\\069\000\103\000\070\000\002\000\073\000\232\000\076\000\125\000\
\\077\000\124\000\078\000\123\000\079\000\122\000\080\000\121\000\
\\081\000\120\000\082\000\119\000\083\000\118\000\084\000\117\000\
\\085\000\116\000\086\000\115\000\087\000\114\000\088\000\113\000\
\\089\000\112\000\090\000\111\000\101\000\110\000\000\000\
\\086\000\115\000\087\000\169\001\088\000\113\000\089\000\112\000\
\\090\000\111\000\101\000\110\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\073\000\056\001\074\000\176\001\076\000\125\000\077\000\124\000\
\\078\000\123\000\079\000\122\000\080\000\121\000\081\000\120\000\
\\082\000\119\000\083\000\118\000\084\000\117\000\085\000\116\000\
\\086\000\115\000\087\000\114\000\088\000\113\000\089\000\112\000\
\\090\000\111\000\101\000\110\000\000\000\
\\073\000\177\001\076\000\125\000\077\000\124\000\078\000\123\000\
\\079\000\122\000\080\000\121\000\081\000\120\000\082\000\119\000\
\\083\000\118\000\084\000\117\000\085\000\116\000\086\000\115\000\
\\087\000\114\000\088\000\113\000\089\000\112\000\090\000\111\000\
\\101\000\110\000\000\000\
\\092\000\178\001\000\000\
\\000\000\
\\000\000\
\\022\000\180\001\023\000\254\000\024\000\253\000\025\000\252\000\
\\026\000\251\000\027\000\250\000\073\000\151\000\076\000\125\000\
\\077\000\124\000\078\000\123\000\079\000\122\000\080\000\121\000\
\\081\000\120\000\082\000\119\000\083\000\118\000\084\000\117\000\
\\085\000\116\000\086\000\115\000\087\000\114\000\088\000\113\000\
\\089\000\112\000\090\000\111\000\101\000\110\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\098\000\184\001\000\000\
\\000\000\
\\000\000\
\\000\000\
\\041\000\159\000\042\000\161\001\044\000\188\001\045\000\157\000\
\\072\000\156\000\073\000\155\000\076\000\125\000\077\000\124\000\
\\078\000\123\000\079\000\122\000\080\000\121\000\081\000\120\000\
\\082\000\119\000\083\000\118\000\084\000\117\000\085\000\116\000\
\\086\000\115\000\087\000\114\000\088\000\154\000\089\000\112\000\
\\090\000\111\000\101\000\110\000\000\000\
\\000\000\
\\073\000\190\001\076\000\125\000\077\000\124\000\078\000\123\000\
\\079\000\122\000\080\000\121\000\081\000\120\000\082\000\119\000\
\\083\000\118\000\084\000\117\000\085\000\116\000\086\000\115\000\
\\087\000\114\000\088\000\113\000\089\000\112\000\090\000\111\000\
\\101\000\110\000\000\000\
\\052\000\191\001\053\000\117\001\072\000\116\001\088\000\115\001\
\\089\000\112\000\090\000\111\000\101\000\110\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\018\000\034\001\019\000\195\001\000\000\
\\041\000\159\000\042\000\196\001\045\000\157\000\072\000\156\000\
\\073\000\155\000\076\000\125\000\077\000\124\000\078\000\123\000\
\\079\000\122\000\080\000\121\000\081\000\120\000\082\000\119\000\
\\083\000\118\000\084\000\117\000\085\000\116\000\086\000\115\000\
\\087\000\114\000\088\000\154\000\089\000\112\000\090\000\111\000\
\\101\000\110\000\000\000\
\\000\000\
\\073\000\133\001\076\000\125\000\077\000\124\000\078\000\123\000\
\\079\000\122\000\080\000\121\000\081\000\120\000\082\000\119\000\
\\083\000\118\000\084\000\117\000\085\000\116\000\086\000\115\000\
\\087\000\114\000\088\000\113\000\089\000\112\000\090\000\111\000\
\\096\000\197\001\101\000\110\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\101\000\204\001\103\000\203\001\104\000\202\001\105\000\201\001\000\000\
\\000\000\
\\000\000\
\\000\000\
\\046\000\211\001\047\000\210\001\048\000\209\001\049\000\208\001\000\000\
\\000\000\
\\000\000\
\\055\000\217\001\056\000\216\001\057\000\215\001\072\000\214\001\
\\088\000\115\001\089\000\112\000\090\000\111\000\101\000\110\000\000\000\
\\000\000\
\\073\000\218\001\076\000\125\000\077\000\124\000\078\000\123\000\
\\079\000\122\000\080\000\121\000\081\000\120\000\082\000\119\000\
\\083\000\118\000\084\000\117\000\085\000\116\000\086\000\115\000\
\\087\000\114\000\088\000\113\000\089\000\112\000\090\000\111\000\
\\101\000\110\000\000\000\
\\041\000\159\000\042\000\219\001\045\000\157\000\072\000\156\000\
\\073\000\155\000\076\000\125\000\077\000\124\000\078\000\123\000\
\\079\000\122\000\080\000\121\000\081\000\120\000\082\000\119\000\
\\083\000\118\000\084\000\117\000\085\000\116\000\086\000\115\000\
\\087\000\114\000\088\000\154\000\089\000\112\000\090\000\111\000\
\\101\000\110\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\099\000\222\001\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\048\000\228\001\049\000\208\001\000\000\
\\041\000\159\000\042\000\229\001\045\000\157\000\072\000\156\000\
\\073\000\155\000\076\000\125\000\077\000\124\000\078\000\123\000\
\\079\000\122\000\080\000\121\000\081\000\120\000\082\000\119\000\
\\083\000\118\000\084\000\117\000\085\000\116\000\086\000\115\000\
\\087\000\114\000\088\000\154\000\089\000\112\000\090\000\111\000\
\\101\000\110\000\000\000\
\\046\000\230\001\047\000\210\001\048\000\209\001\049\000\208\001\000\000\
\\000\000\
\\000\000\
\\073\000\233\001\076\000\125\000\077\000\124\000\078\000\123\000\
\\079\000\122\000\080\000\121\000\081\000\120\000\082\000\119\000\
\\083\000\118\000\084\000\117\000\085\000\116\000\086\000\115\000\
\\087\000\114\000\088\000\113\000\089\000\112\000\090\000\111\000\
\\101\000\110\000\000\000\
\\058\000\234\001\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\041\000\159\000\042\000\241\001\045\000\157\000\072\000\156\000\
\\073\000\155\000\076\000\125\000\077\000\124\000\078\000\123\000\
\\079\000\122\000\080\000\121\000\081\000\120\000\082\000\119\000\
\\083\000\118\000\084\000\117\000\085\000\116\000\086\000\115\000\
\\087\000\114\000\088\000\154\000\089\000\112\000\090\000\111\000\
\\101\000\110\000\000\000\
\\000\000\
\\000\000\
\\101\000\204\001\103\000\203\001\104\000\242\001\105\000\201\001\000\000\
\\101\000\204\001\103\000\203\001\105\000\243\001\000\000\
\\073\000\244\001\076\000\125\000\077\000\124\000\078\000\123\000\
\\079\000\122\000\080\000\121\000\081\000\120\000\082\000\119\000\
\\083\000\118\000\084\000\117\000\085\000\116\000\086\000\115\000\
\\087\000\114\000\088\000\113\000\089\000\112\000\090\000\111\000\
\\101\000\110\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\006\000\012\000\007\000\011\000\010\000\010\000\012\000\009\000\
\\013\000\008\000\014\000\007\000\020\000\163\000\028\000\162\000\
\\035\000\246\001\036\000\160\000\041\000\159\000\042\000\158\000\
\\045\000\157\000\069\000\003\000\070\000\002\000\072\000\156\000\
\\073\000\155\000\076\000\125\000\077\000\124\000\078\000\123\000\
\\079\000\122\000\080\000\121\000\081\000\120\000\082\000\119\000\
\\083\000\118\000\084\000\117\000\085\000\116\000\086\000\115\000\
\\087\000\114\000\088\000\154\000\089\000\112\000\090\000\111\000\
\\094\000\001\000\101\000\110\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\073\000\248\001\076\000\125\000\077\000\124\000\078\000\123\000\
\\079\000\122\000\080\000\121\000\081\000\120\000\082\000\119\000\
\\083\000\118\000\084\000\117\000\085\000\116\000\086\000\115\000\
\\087\000\114\000\088\000\113\000\089\000\112\000\090\000\111\000\
\\101\000\110\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\056\000\250\001\057\000\215\001\072\000\214\001\088\000\115\001\
\\089\000\112\000\090\000\111\000\101\000\110\000\000\000\
\\018\000\034\001\019\000\251\001\000\000\
\\000\000\
\\000\000\
\\100\000\253\001\000\000\
\\000\000\
\\000\000\
\\101\000\000\002\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\041\000\159\000\042\000\002\002\045\000\157\000\072\000\156\000\
\\073\000\155\000\076\000\125\000\077\000\124\000\078\000\123\000\
\\079\000\122\000\080\000\121\000\081\000\120\000\082\000\119\000\
\\083\000\118\000\084\000\117\000\085\000\116\000\086\000\115\000\
\\087\000\114\000\088\000\154\000\089\000\112\000\090\000\111\000\
\\101\000\110\000\000\000\
\\000\000\
\\000\000\
\\101\000\004\002\102\000\003\002\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\073\000\007\002\076\000\125\000\077\000\124\000\078\000\123\000\
\\079\000\122\000\080\000\121\000\081\000\120\000\082\000\119\000\
\\083\000\118\000\084\000\117\000\085\000\116\000\086\000\115\000\
\\087\000\114\000\088\000\113\000\089\000\112\000\090\000\111\000\
\\101\000\110\000\000\000\
\\101\000\004\002\102\000\008\002\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\"
val numstates = 523
val numrules = 300
val s = Unsynchronized.ref "" and index = Unsynchronized.ref 0
val string_to_int = fn () => 
let val i = !index
in index := i+2; Char.ord(String.sub(!s,i)) + Char.ord(String.sub(!s,i+1)) * 256
end
val string_to_list = fn s' =>
    let val len = String.size s'
        fun f () =
           if !index < len then string_to_int() :: f()
           else nil
   in index := 0; s := s'; f ()
   end
val string_to_pairlist = fn (conv_key,conv_entry) =>
     let fun f () =
         case string_to_int()
         of 0 => EMPTY
          | n => PAIR(conv_key (n-1),conv_entry (string_to_int()),f())
     in f
     end
val string_to_pairlist_default = fn (conv_key,conv_entry) =>
    let val conv_row = string_to_pairlist(conv_key,conv_entry)
    in fn () =>
       let val default = conv_entry(string_to_int())
           val row = conv_row()
       in (row,default)
       end
   end
val string_to_table = fn (convert_row,s') =>
    let val len = String.size s'
        fun f ()=
           if !index < len then convert_row() :: f()
           else nil
     in (s := s'; index := 0; f ())
     end
local
  val memo = Array.array(numstates+numrules,ERROR)
  val _ =let fun g i=(Array.update(memo,i,REDUCE(i-numstates)); g(i+1))
       fun f i =
            if i=numstates then g i
            else (Array.update(memo,i,SHIFT (STATE i)); f (i+1))
          in f 0 handle Subscript => ()
          end
in
val entry_to_action = fn 0 => ACCEPT | 1 => ERROR | j => Array.sub(memo,(j-2))
end
val gotoT=Array.fromList(string_to_table(string_to_pairlist(NT,STATE),gotoT))
val actionRows=string_to_table(string_to_pairlist_default(T,entry_to_action),actionRows)
val actionRowNumbers = string_to_list actionRowNumbers
val actionT = let val actionRowLookUp=
let val a=Array.fromList(actionRows) in fn i=>Array.sub(a,i) end
in Array.fromList(map actionRowLookUp actionRowNumbers)
end
in LrTable.mkLrTable {actions=actionT,gotos=gotoT,numRules=numrules,
numStates=numstates,initialState=STATE 0}
end
end
local open Header in
type pos = SourcePos.t
type arg =  ( SourceFile.t * Proof.context ) 
structure MlyValue = 
struct
datatype svalue = VOID' | ntVOID of unit ->  unit
 | STRING_LITERAL of unit ->  (string)
 | NUMERIC_CONSTANT of unit ->  (Absyn.numliteral_info)
 | TYPEID of unit ->  (string) | ID of unit ->  (string)
 | calls_block of unit ->  (string wrap list option)
 | namedstringexplist1 of unit ->  (namedstringexp list)
 | namedstringexplist of unit ->  (namedstringexp list)
 | namedstringexp of unit ->  (namedstringexp)
 | stringlist1 of unit ->  (string list)
 | cstring_literal of unit ->  (string wrap)
 | asmmod3 of unit ->  (string list)
 | asmmod2 of unit ->  (namedstringexp list*string list)
 | asmmod1 of unit ->  (namedstringexp list*namedstringexp list*string list)
 | asmblock of unit ->  (asmblock)
 | attribute_parameter_list1 of unit ->  (expr list)
 | attribute_list of unit ->  (gcc_attribute list)
 | attribute_specifier of unit ->  (gcc_attribute list wrap)
 | attribute of unit ->  (gcc_attribute)
 | fieldlist of unit ->  (string list)
 | idlist of unit ->  (string wrap list)
 | constant of unit ->  (literalconstant)
 | primary_expression of unit ->  (expr)
 | postfix_expression of unit ->  (expr)
 | cast_expression of unit ->  (expr)
 | unary_expression of unit ->  (expr)
 | multiplicative_expression of unit ->  (expr)
 | shift_expression of unit ->  (expr)
 | additive_expression of unit ->  (expr)
 | relational_expression of unit ->  (expr)
 | equality_expression of unit ->  (expr)
 | AND_expression of unit ->  (expr)
 | exclusive_OR_expression of unit ->  (expr)
 | inclusive_OR_expression of unit ->  (expr)
 | logical_OR_expression of unit ->  (expr)
 | logical_AND_expression of unit ->  (expr)
 | opt_rexpr_list of unit ->  (expr list wrap)
 | rexpr_list of unit ->  (expr list wrap)
 | rexpression of unit ->  (expr) | lexpression of unit ->  (expr)
 | struct_id of unit ->  (string wrap)
 | struct_or_union_specifier of unit ->  (struct_or_union_specifier)
 | type_specifier of unit ->  (type_specifier)
 | asm_declarator_mod of unit ->  (unit)
 | direct_declarator of unit ->  (addecl wrap)
 | init_declarator_list of unit ->  ( ( addecl wrap * initializer option )  wrap list)
 | init_declarator of unit ->  ( ( addecl wrap * initializer option )  wrap)
 | struct_declarator_list of unit ->  ( ( addecl wrap * expr option )  list wrap)
 | struct_declarator of unit ->  ( ( addecl wrap * expr option )  wrap)
 | direct_abstract_declarator of unit ->  (adecl)
 | abstract_declarator of unit ->  (adecl)
 | declarator of unit ->  (addecl wrap) | pointer of unit ->  (adecl)
 | assignop of unit ->  (binoptype option)
 | opt_for3_exprbase of unit ->  (statement)
 | opt_for3_expr0 of unit ->  (statement list)
 | opt_for3_expr of unit ->  (statement)
 | opt_for2_expr of unit ->  (expr)
 | opt_for1_exprbase of unit ->  (statement)
 | opt_for1_expr0 of unit ->  (statement list)
 | opt_for1_expr of unit ->  (statement)
 | opt_for1_bitem of unit ->  (block_item list)
 | label of unit ->  (expr option wrap)
 | labellist of unit ->  (expr option wrap list wrap)
 | switchcase of unit ->  ( ( expr option wrap list wrap * block_item list ) )
 | switchcase_list of unit ->  ( ( expr option wrap list wrap * block_item list )  list)
 | statement_label of unit ->  (string wrap)
 | statement_list1 of unit ->  (statement list)
 | statement_list of unit ->  (statement list)
 | statement of unit ->  (statement)
 | compound_statement of unit ->  (block_item list wrap)
 | function_definition of unit ->  (ext_decl)
 | parameter_list1 of unit ->  ( ( expr ctype  * string wrap option )  wrap list wrap)
 | parameter_list of unit ->  ( ( expr ctype * string wrap option )  wrap list wrap)
 | parameter_declaration of unit ->  ( ( expr ctype * string wrap option )  wrap)
 | block_item of unit ->  (block_item list)
 | block_item_list of unit ->  (block_item list)
 | type_name of unit ->  (expr ctype wrap)
 | integral_type of unit ->  (inttype wrap)
 | elementary_type of unit ->  (expr ctype)
 | type_definition of unit ->  (declaration)
 | struct_declaration of unit ->  (struct_fields wrap*struct_id_decl wrap list)
 | struct_declaration_list of unit ->  (struct_fields wrap*struct_id_decl wrap list)
 | declaration of unit ->  (declaration wrap list)
 | designator of unit ->  (designator)
 | designator_list of unit ->  (designator list)
 | designation of unit ->  (designator list)
 | initializer of unit ->  (initializer wrap)
 | dinitializer of unit ->  ( ( designator list * initializer ) )
 | initializer_list of unit ->  ( ( designator list * initializer )  list)
 | specifier_qualifier_list of unit ->  (decl_specifier list wrap)
 | declaration_specifiers of unit ->  (decl_specifier list wrap)
 | invariant_option of unit ->  (string wrap option)
 | invariant of unit ->  (string wrap)
 | modlist of unit ->  (string wrap list)
 | rel_spec of unit ->  (string wrap)
 | fnspecs of unit ->  (string wrap)
 | special_function_specs of unit ->  (fnspec wrap list wrap)
 | special_function_spec of unit ->  (fnspec wrap)
 | function_specifiers of unit ->  (fnspec wrap list wrap)
 | type_qualifier_list of unit ->  (type_qualifier wrap list)
 | type_qualifier of unit ->  (type_qualifier wrap)
 | enumerator of unit ->  ( ( string wrap * expr option ) )
 | enumerator_list of unit ->  ( ( string wrap * expr option )  list)
 | enum_specifier of unit ->  (enum_specifier)
 | storage_class_specifier of unit ->  (storage_class_specifier wrap)
 | optvolatile of unit ->  (bool)
 | optfnspec of unit ->  (string option wrap)
 | external_declaration of unit ->  (ext_decl list)
 | translation_unit of unit ->  (ext_decl list)
 | begin of unit ->  (ext_decl list)
end
type svalue = MlyValue.svalue
type result = ext_decl list
end
structure EC=
struct
open LrTable
val is_keyword =
fn (T 49) => true | (T 37) => true | (T 38) => true | (T 35) => true
 | (T 75) => true | (T 39) => true | (T 36) => true | (T 62) => true
 | (T 64) => true | (T 65) => true | (T 66) => true | (T 67) => true
 | (T 69) => true | (T 77) => true | (T 11) => true | (T 6) => true | 
(T 7) => true | _ => false
val preferred_change = 
(nil
,(T 11) :: nil
)::
nil
val noShift = 
fn (T 0) => true | _ => false
val showTerminal =
fn (T 0) => "EOF"
  | (T 1) => "YSTAR"
  | (T 2) => "SLASH"
  | (T 3) => "MOD"
  | (T 4) => "LPAREN"
  | (T 5) => "RPAREN"
  | (T 6) => "LCURLY"
  | (T 7) => "RCURLY"
  | (T 8) => "LBRACKET"
  | (T 9) => "RBRACKET"
  | (T 10) => "YCOMMA"
  | (T 11) => "YSEMI"
  | (T 12) => "YCOLON"
  | (T 13) => "QMARK"
  | (T 14) => "YEQ"
  | (T 15) => "YDOT"
  | (T 16) => "YPLUS"
  | (T 17) => "YMINUS"
  | (T 18) => "YAND"
  | (T 19) => "YNOT"
  | (T 20) => "YAMPERSAND"
  | (T 21) => "YBITNOT"
  | (T 22) => "PLUSPLUS"
  | (T 23) => "MINUSMINUS"
  | (T 24) => "PLUSEQ"
  | (T 25) => "MINUSEQ"
  | (T 26) => "BANDEQ"
  | (T 27) => "BOREQ"
  | (T 28) => "MULEQ"
  | (T 29) => "DIVEQ"
  | (T 30) => "MODEQ"
  | (T 31) => "BXOREQ"
  | (T 32) => "LSHIFTEQ"
  | (T 33) => "RSHIFTEQ"
  | (T 34) => "YENUM"
  | (T 35) => "YIF"
  | (T 36) => "YELSE"
  | (T 37) => "YWHILE"
  | (T 38) => "YDO"
  | (T 39) => "YRETURN"
  | (T 40) => "YBREAK"
  | (T 41) => "YCONTINUE"
  | (T 42) => "YGOTO"
  | (T 43) => "YFOR"
  | (T 44) => "SWITCH"
  | (T 45) => "CASE"
  | (T 46) => "DEFAULT"
  | (T 47) => "YSIZEOF"
  | (T 48) => "YTYPEOF"
  | (T 49) => "YOFFSETOF"
  | (T 50) => "LOGICALOR"
  | (T 51) => "LOGICALAND"
  | (T 52) => "BITWISEOR"
  | (T 53) => "BITWISEXOR"
  | (T 54) => "EQUALS"
  | (T 55) => "NOTEQUALS"
  | (T 56) => "YLE"
  | (T 57) => "YGE"
  | (T 58) => "YLESS"
  | (T 59) => "YGREATER"
  | (T 60) => "LEFTSHIFT"
  | (T 61) => "RIGHTSHIFT"
  | (T 62) => "INT"
  | (T 63) => "BOOL"
  | (T 64) => "CHAR"
  | (T 65) => "LONG"
  | (T 66) => "INT128"
  | (T 67) => "SHORT"
  | (T 68) => "SIGNED"
  | (T 69) => "UNSIGNED"
  | (T 70) => "VOID"
  | (T 71) => "ARROW"
  | (T 72) => "ID"
  | (T 73) => "TYPEID"
  | (T 74) => "NUMERIC_CONSTANT"
  | (T 75) => "STRUCT"
  | (T 76) => "UNION"
  | (T 77) => "TYPEDEF"
  | (T 78) => "EXTERN"
  | (T 79) => "CONST"
  | (T 80) => "VOLATILE"
  | (T 81) => "RESTRICT"
  | (T 82) => "INVARIANT"
  | (T 83) => "INLINE"
  | (T 84) => "STATIC"
  | (T 85) => "NORETURN"
  | (T 86) => "THREAD_LOCAL"
  | (T 87) => "AUTO"
  | (T 88) => "FNSPEC"
  | (T 89) => "RELSPEC"
  | (T 90) => "AUXUPD"
  | (T 91) => "GHOSTUPD"
  | (T 92) => "MODIFIES"
  | (T 93) => "CALLS"
  | (T 94) => "OWNED_BY"
  | (T 95) => "SPEC_BEGIN"
  | (T 96) => "SPEC_END"
  | (T 97) => "DONT_TRANSLATE"
  | (T 98) => "STRING_LITERAL"
  | (T 99) => "SPEC_BLOCKEND"
  | (T 100) => "GCC_ATTRIBUTE"
  | (T 101) => "YASM"
  | (T 102) => "YREGISTER"
  | _ => "bogus-term"
local open Header in
val errtermvalue=
fn _ => MlyValue.VOID'
end
val terms = (T 0) :: (T 1) :: (T 2) :: (T 3) :: (T 4) :: (T 5) :: (T 6
) :: (T 7) :: (T 8) :: (T 9) :: (T 10) :: (T 11) :: (T 12) :: (T 13)
 :: (T 14) :: (T 15) :: (T 16) :: (T 17) :: (T 18) :: (T 19) :: (T 20)
 :: (T 21) :: (T 22) :: (T 23) :: (T 24) :: (T 25) :: (T 26) :: (T 27)
 :: (T 28) :: (T 29) :: (T 30) :: (T 31) :: (T 32) :: (T 33) :: (T 34)
 :: (T 35) :: (T 36) :: (T 37) :: (T 38) :: (T 39) :: (T 40) :: (T 41)
 :: (T 42) :: (T 43) :: (T 44) :: (T 45) :: (T 46) :: (T 47) :: (T 48)
 :: (T 49) :: (T 50) :: (T 51) :: (T 52) :: (T 53) :: (T 54) :: (T 55)
 :: (T 56) :: (T 57) :: (T 58) :: (T 59) :: (T 60) :: (T 61) :: (T 62)
 :: (T 63) :: (T 64) :: (T 65) :: (T 66) :: (T 67) :: (T 68) :: (T 69)
 :: (T 70) :: (T 71) :: (T 75) :: (T 76) :: (T 77) :: (T 78) :: (T 79)
 :: (T 80) :: (T 81) :: (T 82) :: (T 83) :: (T 84) :: (T 85) :: (T 86)
 :: (T 87) :: (T 88) :: (T 89) :: (T 90) :: (T 91) :: (T 92) :: (T 93)
 :: (T 94) :: (T 95) :: (T 96) :: (T 97) :: (T 99) :: (T 100) :: (T 
101) :: (T 102) :: nil
end
structure Actions =
struct 
type int = Int.int
exception mlyAction of int
local open Header in
val actions = 
fn (i392:int,defaultPos,stack,
    (source, ctxt):arg) =>
case (i392,stack)
of (0,(_,(MlyValue.translation_unit translation_unit1,
translation_unit1left,translation_unit1right))::rest671) => let val 
result=MlyValue.begin(fn _ => let val translation_unit as 
translation_unit1=translation_unit1 ()
 in (translation_unit) end
)
 in (LrTable.NT 0,(result,translation_unit1left,translation_unit1right
),rest671) end
| (1,(_,(MlyValue.external_declaration external_declaration1,
external_declaration1left,external_declaration1right))::rest671) => 
let val result=MlyValue.translation_unit(fn _ => let val 
external_declaration as external_declaration1=external_declaration1 ()
 in (external_declaration) end
)
 in (LrTable.NT 1,(result,external_declaration1left,
external_declaration1right),rest671) end
| (2,(_,(MlyValue.translation_unit translation_unit1,_,
translation_unit1right))::(_,(MlyValue.external_declaration 
external_declaration1,external_declaration1left,_))::rest671) => let 
val result=MlyValue.translation_unit(fn _ => let val 
external_declaration as external_declaration1=external_declaration1 ()
val translation_unit as translation_unit1=translation_unit1 ()
 in (external_declaration @ translation_unit) end
)
 in (LrTable.NT 1,(result,external_declaration1left,
translation_unit1right),rest671) end
| (3,(_,(MlyValue.function_definition function_definition1,
function_definition1left,function_definition1right))::rest671) => let 
val result=MlyValue.external_declaration(fn _ => let val 
function_definition as function_definition1=function_definition1 ()
 in ([function_definition]) end
)
 in (LrTable.NT 2,(result,function_definition1left,
function_definition1right),rest671) end
| (4,(_,(MlyValue.declaration declaration1,declaration1left,
declaration1right))::rest671) => let val result=
MlyValue.external_declaration(fn _ => let val declaration as 
declaration1=declaration1 ()
 in (map Decl declaration) end
)
 in (LrTable.NT 2,(result,declaration1left,declaration1right),rest671)
 end
| (5,(_,(_,YSEMI1left,YSEMI1right))::rest671) => let val result=
MlyValue.external_declaration(fn _ => ([]))
 in (LrTable.NT 2,(result,YSEMI1left,YSEMI1right),rest671) end
| (6,(_,(_,TYPEDEFleft as TYPEDEF1left,TYPEDEFright as TYPEDEF1right))
::rest671) => let val result=MlyValue.storage_class_specifier(fn _ => 
(wrap(TypeDef, TYPEDEFleft, TYPEDEFright)))
 in (LrTable.NT 5,(result,TYPEDEF1left,TYPEDEF1right),rest671) end
| (7,(_,(_,EXTERNleft as EXTERN1left,EXTERNright as EXTERN1right))::
rest671) => let val result=MlyValue.storage_class_specifier(fn _ => (
wrap(Extern, EXTERNleft, EXTERNright)))
 in (LrTable.NT 5,(result,EXTERN1left,EXTERN1right),rest671) end
| (8,(_,(_,STATICleft as STATIC1left,STATICright as STATIC1right))::
rest671) => let val result=MlyValue.storage_class_specifier(fn _ => (
wrap(Static, STATICleft, STATICright)))
 in (LrTable.NT 5,(result,STATIC1left,STATIC1right),rest671) end
| (9,(_,(_,YREGISTERleft as YREGISTER1left,YREGISTERright as 
YREGISTER1right))::rest671) => let val result=
MlyValue.storage_class_specifier(fn _ => (
wrap(Register, YREGISTERleft, YREGISTERright)))
 in (LrTable.NT 5,(result,YREGISTER1left,YREGISTER1right),rest671) end
| (10,(_,(_,AUTOleft as AUTO1left,AUTOright as AUTO1right))::rest671)
 => let val result=MlyValue.storage_class_specifier(fn _ => (
wrap(Auto, AUTOleft, AUTOright)))
 in (LrTable.NT 5,(result,AUTO1left,AUTO1right),rest671) end
| (11,(_,(_,THREAD_LOCALleft as THREAD_LOCAL1left,THREAD_LOCALright
 as THREAD_LOCAL1right))::rest671) => let val result=
MlyValue.storage_class_specifier(fn _ => (
wrap(Thread_Local, THREAD_LOCALleft,
                                             THREAD_LOCALright)
))
 in (LrTable.NT 5,(result,THREAD_LOCAL1left,THREAD_LOCAL1right),
rest671) end
| (12,(_,(_,INLINEleft as INLINE1left,INLINEright as INLINE1right))::
rest671) => let val result=MlyValue.function_specifiers(fn _ => (
wrap([], INLINEleft, INLINEright)))
 in (LrTable.NT 11,(result,INLINE1left,INLINE1right),rest671) end
| (13,(_,(_,NORETURNleft as NORETURN1left,NORETURNright as 
NORETURN1right))::rest671) => let val result=
MlyValue.function_specifiers(fn _ => (
wrap([wrap(gcc_attribs [GCC_AttribID "noreturn"],
                            NORETURNleft, NORETURNright)],
                      NORETURNleft, NORETURNright)
))
 in (LrTable.NT 11,(result,NORETURN1left,NORETURN1right),rest671) end
| (14,(_,(_,_,SPEC_BLOCKEND1right))::(_,(
MlyValue.special_function_specs special_function_specs1,
special_function_specs1left,_))::rest671) => let val result=
MlyValue.function_specifiers(fn _ => let val special_function_specs
 as special_function_specs1=special_function_specs1 ()
 in (special_function_specs) end
)
 in (LrTable.NT 11,(result,special_function_specs1left,
SPEC_BLOCKEND1right),rest671) end
| (15,(_,(MlyValue.attribute_specifier attribute_specifier1,
attribute_specifier1left,attribute_specifier1right))::rest671) => let 
val result=MlyValue.function_specifiers(fn _ => let val 
attribute_specifier as attribute_specifier1=attribute_specifier1 ()
 in (
wrap ([apnode gcc_attribs attribute_specifier],
                       left attribute_specifier,
                       right attribute_specifier)
) end
)
 in (LrTable.NT 11,(result,attribute_specifier1left,
attribute_specifier1right),rest671) end
| (16,(_,(_,_,RPAREN2right))::_::(_,(MlyValue.attribute_list 
attribute_list1,_,_))::_::_::(_,(_,GCC_ATTRIBUTEleft as 
GCC_ATTRIBUTE1left,_))::rest671) => let val result=
MlyValue.attribute_specifier(fn _ => let val attribute_list as 
attribute_list1=attribute_list1 ()
 in (wrap(attribute_list, GCC_ATTRIBUTEleft, RPAREN2right)) end
)
 in (LrTable.NT 93,(result,GCC_ATTRIBUTE1left,RPAREN2right),rest671)
 end
| (17,(_,(_,_,SPEC_BLOCKENDright as SPEC_BLOCKEND1right))::(_,(
MlyValue.ID ID1,_,_))::(_,(_,OWNED_BYleft as OWNED_BY1left,_))::
rest671) => let val result=MlyValue.attribute_specifier(fn _ => let 
val ID as ID1=ID1 ()
 in (wrap([OWNED_BY ID], OWNED_BYleft, SPEC_BLOCKENDright)) end
)
 in (LrTable.NT 93,(result,OWNED_BY1left,SPEC_BLOCKEND1right),rest671)
 end
| (18,rest671) => let val result=MlyValue.attribute_list(fn _ => ([]))
 in (LrTable.NT 94,(result,defaultPos,defaultPos),rest671) end
| (19,(_,(MlyValue.attribute attribute1,attribute1left,attribute1right
))::rest671) => let val result=MlyValue.attribute_list(fn _ => let 
val attribute as attribute1=attribute1 ()
 in ([attribute]) end
)
 in (LrTable.NT 94,(result,attribute1left,attribute1right),rest671)
 end
| (20,(_,(MlyValue.attribute_list attribute_list1,_,
attribute_list1right))::_::(_,(MlyValue.attribute attribute1,
attribute1left,_))::rest671) => let val result=MlyValue.attribute_list
(fn _ => let val attribute as attribute1=attribute1 ()
val attribute_list as attribute_list1=attribute_list1 ()
 in (attribute :: attribute_list) end
)
 in (LrTable.NT 94,(result,attribute1left,attribute_list1right),
rest671) end
| (21,(_,(MlyValue.ID ID1,ID1left,ID1right))::rest671) => let val 
result=MlyValue.attribute(fn _ => let val ID as ID1=ID1 ()
 in (
let val idstr = if String.isPrefix "__" ID andalso
                                    String.sub(ID,size ID - 1) = #"_" andalso
                                    String.sub(ID,size ID - 2) = #"_" andalso
                                    size ID > 4
                                 then
                                   String.substring(ID,2,size ID - 4)
                                 else ID
                 in
                   GCC_AttribID idstr
                 end
) end
)
 in (LrTable.NT 92,(result,ID1left,ID1right),rest671) end
| (22,(_,(_,CONST1left,CONST1right))::rest671) => let val result=
MlyValue.attribute(fn _ => (GCC_AttribID "const"))
 in (LrTable.NT 92,(result,CONST1left,CONST1right),rest671) end
| (23,(_,(_,_,RPAREN1right))::_::(_,(MlyValue.ID ID1,ID1left,_))::
rest671) => let val result=MlyValue.attribute(fn _ => let val ID as 
ID1=ID1 ()
 in (GCC_AttribFn (ID, [])) end
)
 in (LrTable.NT 92,(result,ID1left,RPAREN1right),rest671) end
| (24,(_,(_,_,RPAREN1right))::(_,(MlyValue.attribute_parameter_list1 
attribute_parameter_list11,_,_))::_::(_,(MlyValue.ID ID1,ID1left,_))::
rest671) => let val result=MlyValue.attribute(fn _ => let val ID as 
ID1=ID1 ()
val attribute_parameter_list1 as attribute_parameter_list11=
attribute_parameter_list11 ()
 in (GCC_AttribFn (ID, attribute_parameter_list1)) end
)
 in (LrTable.NT 92,(result,ID1left,RPAREN1right),rest671) end
| (25,(_,(MlyValue.rexpression rexpression1,rexpression1left,
rexpression1right))::rest671) => let val result=
MlyValue.attribute_parameter_list1(fn _ => let val rexpression as 
rexpression1=rexpression1 ()
 in ([rexpression]) end
)
 in (LrTable.NT 95,(result,rexpression1left,rexpression1right),rest671
) end
| (26,(_,(MlyValue.attribute_parameter_list1 
attribute_parameter_list11,_,attribute_parameter_list11right))::_::(_,
(MlyValue.rexpression rexpression1,rexpression1left,_))::rest671) => 
let val result=MlyValue.attribute_parameter_list1(fn _ => let val 
rexpression as rexpression1=rexpression1 ()
val attribute_parameter_list1 as attribute_parameter_list11=
attribute_parameter_list11 ()
 in (rexpression :: attribute_parameter_list1) end
)
 in (LrTable.NT 95,(result,rexpression1left,
attribute_parameter_list11right),rest671) end
| (27,(_,(MlyValue.special_function_spec special_function_spec1,
special_function_spec1left,special_function_spec1right))::rest671) => 
let val result=MlyValue.special_function_specs(fn _ => let val 
special_function_spec as special_function_spec1=special_function_spec1
 ()
 in (
wrap([special_function_spec], left special_function_spec,
                      right special_function_spec)
) end
)
 in (LrTable.NT 13,(result,special_function_spec1left,
special_function_spec1right),rest671) end
| (28,(_,(MlyValue.special_function_specs special_function_specs1,_,
special_function_specs1right))::(_,(MlyValue.special_function_spec 
special_function_spec1,special_function_spec1left,_))::rest671) => 
let val result=MlyValue.special_function_specs(fn _ => let val 
special_function_spec as special_function_spec1=special_function_spec1
 ()
val special_function_specs as special_function_specs1=
special_function_specs1 ()
 in (
wrap (special_function_spec :: node special_function_specs,
                       left special_function_spec,
                       right special_function_specs)
) end
)
 in (LrTable.NT 13,(result,special_function_spec1left,
special_function_specs1right),rest671) end
| (29,(_,(MlyValue.idlist idlist1,_,idlist1right))::(_,(_,MODIFIESleft
 as MODIFIES1left,MODIFIESright))::rest671) => let val result=
MlyValue.special_function_spec(fn _ => let val idlist as idlist1=
idlist1 ()
 in (
case idlist of
                     [] => wrap(fn_modifies [], MODIFIESleft, MODIFIESright)
                   | _ => wrap(fn_modifies (map node idlist),
                               MODIFIESleft,
                               right (List.last idlist))
) end
)
 in (LrTable.NT 12,(result,MODIFIES1left,idlist1right),rest671) end
| (30,(_,(MlyValue.fnspecs fnspecs1,_,fnspecs1right))::(_,(_,
FNSPECleft as FNSPEC1left,_))::rest671) => let val result=
MlyValue.special_function_spec(fn _ => let val fnspecs as fnspecs1=
fnspecs1 ()
 in (wrap(fnspec fnspecs, FNSPECleft, right fnspecs)) end
)
 in (LrTable.NT 12,(result,FNSPEC1left,fnspecs1right),rest671) end
| (31,(_,(MlyValue.rel_spec rel_spec1,_,rel_spec1right))::(_,(_,
RELSPECleft as RELSPEC1left,_))::rest671) => let val result=
MlyValue.special_function_spec(fn _ => let val rel_spec as rel_spec1=
rel_spec1 ()
 in (wrap(relspec rel_spec, RELSPECleft, right rel_spec)) end
)
 in (LrTable.NT 12,(result,RELSPEC1left,rel_spec1right),rest671) end
| (32,(_,(_,DONT_TRANSLATEleft as DONT_TRANSLATE1left,
DONT_TRANSLATEright as DONT_TRANSLATE1right))::rest671) => let val 
result=MlyValue.special_function_spec(fn _ => (
wrap(didnt_translate, DONT_TRANSLATEleft, DONT_TRANSLATEright)))
 in (LrTable.NT 12,(result,DONT_TRANSLATE1left,DONT_TRANSLATE1right),
rest671) end
| (33,(_,(MlyValue.STRING_LITERAL STRING_LITERAL1,_,
STRING_LITERALright as STRING_LITERAL1right))::_::(_,(MlyValue.ID ID1,
IDleft as ID1left,_))::rest671) => let val result=MlyValue.fnspecs(fn 
_ => let val ID as ID1=ID1 ()
val STRING_LITERAL as STRING_LITERAL1=STRING_LITERAL1 ()
 in (
wrap(ID ^ ": \"" ^ STRING_LITERAL ^ "\"", IDleft,
                      STRING_LITERALright)
) end
)
 in (LrTable.NT 14,(result,ID1left,STRING_LITERAL1right),rest671) end
| (34,(_,(MlyValue.fnspecs fnspecs1,_,fnspecs1right))::(_,(
MlyValue.STRING_LITERAL STRING_LITERAL1,_,_))::_::(_,(MlyValue.ID ID1,
IDleft as ID1left,_))::rest671) => let val result=MlyValue.fnspecs(fn 
_ => let val ID as ID1=ID1 ()
val STRING_LITERAL as STRING_LITERAL1=STRING_LITERAL1 ()
val fnspecs as fnspecs1=fnspecs1 ()
 in (
wrap((ID ^ ": \"" ^ STRING_LITERAL ^ "\"\n" ^ node fnspecs,
                      IDleft,
                      right fnspecs))
) end
)
 in (LrTable.NT 14,(result,ID1left,fnspecs1right),rest671) end
| (35,(_,(MlyValue.STRING_LITERAL STRING_LITERAL1,STRING_LITERALleft
 as STRING_LITERAL1left,STRING_LITERALright as STRING_LITERAL1right))
::rest671) => let val result=MlyValue.rel_spec(fn _ => let val 
STRING_LITERAL as STRING_LITERAL1=STRING_LITERAL1 ()
 in (
wrap("\"" ^ STRING_LITERAL ^ "\"", STRING_LITERALleft,
                       STRING_LITERALright)
) end
)
 in (LrTable.NT 15,(result,STRING_LITERAL1left,STRING_LITERAL1right),
rest671) end
| (36,rest671) => let val result=MlyValue.idlist(fn _ => ([]))
 in (LrTable.NT 90,(result,defaultPos,defaultPos),rest671) end
| (37,(_,(MlyValue.idlist idlist1,_,idlist1right))::(_,(MlyValue.ID 
ID1,IDleft as ID1left,IDright))::rest671) => let val result=
MlyValue.idlist(fn _ => let val ID as ID1=ID1 ()
val idlist as idlist1=idlist1 ()
 in (wrap(ID,IDleft,IDright) :: idlist) end
)
 in (LrTable.NT 90,(result,ID1left,idlist1right),rest671) end
| (38,(_,(MlyValue.idlist idlist1,_,idlist1right))::(_,(_,_,
RBRACKETright))::_::(_,(_,LBRACKETleft as LBRACKET1left,_))::rest671)
 => let val result=MlyValue.idlist(fn _ => let val idlist as idlist1=
idlist1 ()
 in (
wrap(NameGeneration.phantom_state_name, LBRACKETleft,
                      RBRACKETright) :: idlist
) end
)
 in (LrTable.NT 90,(result,LBRACKET1left,idlist1right),rest671) end
| (39,(_,(_,_,YSEMI1right))::(_,(MlyValue.declaration_specifiers 
declaration_specifiers1,declaration_specifiers1left,_))::rest671) => 
let val result=MlyValue.declaration(fn _ => let val 
declaration_specifiers as declaration_specifiers1=
declaration_specifiers1 ()
 in (empty_declarator ctxt (node declaration_specifiers)) end
)
 in (LrTable.NT 27,(result,declaration_specifiers1left,YSEMI1right),
rest671) end
| (40,(_,(_,_,YSEMI1right))::(_,(MlyValue.init_declarator_list 
init_declarator_list1,_,_))::(_,(MlyValue.declaration_specifiers 
declaration_specifiers1,declaration_specifiers1left,_))::rest671) => 
let val result=MlyValue.declaration(fn _ => let val 
declaration_specifiers as declaration_specifiers1=
declaration_specifiers1 ()
val init_declarator_list as init_declarator_list1=
init_declarator_list1 ()
 in (make_declaration ctxt declaration_specifiers init_declarator_list
) end
)
 in (LrTable.NT 27,(result,declaration_specifiers1left,YSEMI1right),
rest671) end
| (41,(_,(MlyValue.storage_class_specifier storage_class_specifier1,
storage_class_specifier1left,storage_class_specifier1right))::rest671)
 => let val result=MlyValue.declaration_specifiers(fn _ => let val 
storage_class_specifier as storage_class_specifier1=
storage_class_specifier1 ()
 in (
wrap([Storage storage_class_specifier],
                      left storage_class_specifier,
                      right storage_class_specifier)
) end
)
 in (LrTable.NT 19,(result,storage_class_specifier1left,
storage_class_specifier1right),rest671) end
| (42,(_,(MlyValue.declaration_specifiers declaration_specifiers1,_,
declaration_specifiers1right))::(_,(MlyValue.storage_class_specifier 
storage_class_specifier1,storage_class_specifier1left,_))::rest671)
 => let val result=MlyValue.declaration_specifiers(fn _ => let val 
storage_class_specifier as storage_class_specifier1=
storage_class_specifier1 ()
val declaration_specifiers as declaration_specifiers1=
declaration_specifiers1 ()
 in (
wrap(Storage storage_class_specifier ::
                      node declaration_specifiers,
                      left storage_class_specifier,
                      right declaration_specifiers)
) end
)
 in (LrTable.NT 19,(result,storage_class_specifier1left,
declaration_specifiers1right),rest671) end
| (43,(_,(MlyValue.type_specifier type_specifier1,type_specifier1left,
type_specifier1right))::rest671) => let val result=
MlyValue.declaration_specifiers(fn _ => let val type_specifier as 
type_specifier1=type_specifier1 ()
 in (
wrap([TypeSpec type_specifier], tsleft type_specifier,
                      tsright type_specifier)
) end
)
 in (LrTable.NT 19,(result,type_specifier1left,type_specifier1right),
rest671) end
| (44,(_,(MlyValue.declaration_specifiers declaration_specifiers1,_,
declaration_specifiers1right))::(_,(MlyValue.type_specifier 
type_specifier1,type_specifier1left,_))::rest671) => let val result=
MlyValue.declaration_specifiers(fn _ => let val type_specifier as 
type_specifier1=type_specifier1 ()
val declaration_specifiers as declaration_specifiers1=
declaration_specifiers1 ()
 in (
wrap(TypeSpec type_specifier :: node declaration_specifiers,
                      tsleft type_specifier,
                      right declaration_specifiers)
) end
)
 in (LrTable.NT 19,(result,type_specifier1left,
declaration_specifiers1right),rest671) end
| (45,(_,(MlyValue.type_qualifier type_qualifier1,type_qualifier1left,
type_qualifier1right))::rest671) => let val result=
MlyValue.declaration_specifiers(fn _ => let val type_qualifier as 
type_qualifier1=type_qualifier1 ()
 in (
wrap([TypeQual type_qualifier],
                      left type_qualifier,
                      right type_qualifier)
) end
)
 in (LrTable.NT 19,(result,type_qualifier1left,type_qualifier1right),
rest671) end
| (46,(_,(MlyValue.declaration_specifiers declaration_specifiers1,_,
declaration_specifiers1right))::(_,(MlyValue.type_qualifier 
type_qualifier1,type_qualifier1left,_))::rest671) => let val result=
MlyValue.declaration_specifiers(fn _ => let val type_qualifier as 
type_qualifier1=type_qualifier1 ()
val declaration_specifiers as declaration_specifiers1=
declaration_specifiers1 ()
 in (
wrap(TypeQual type_qualifier :: node declaration_specifiers,
                      left type_qualifier,
                      right declaration_specifiers)
) end
)
 in (LrTable.NT 19,(result,type_qualifier1left,
declaration_specifiers1right),rest671) end
| (47,(_,(MlyValue.function_specifiers function_specifiers1,
function_specifiers1left,function_specifiers1right))::rest671) => let 
val result=MlyValue.declaration_specifiers(fn _ => let val 
function_specifiers as function_specifiers1=function_specifiers1 ()
 in (
wrap(map FunSpec (node function_specifiers),
                      left function_specifiers,
                      right function_specifiers)
) end
)
 in (LrTable.NT 19,(result,function_specifiers1left,
function_specifiers1right),rest671) end
| (48,(_,(MlyValue.declaration_specifiers declaration_specifiers1,_,
declaration_specifiers1right))::(_,(MlyValue.function_specifiers 
function_specifiers1,function_specifiers1left,_))::rest671) => let 
val result=MlyValue.declaration_specifiers(fn _ => let val 
function_specifiers as function_specifiers1=function_specifiers1 ()
val declaration_specifiers as declaration_specifiers1=
declaration_specifiers1 ()
 in (
wrap(map FunSpec (node function_specifiers) @
                      node declaration_specifiers,
                      left function_specifiers,
                      right declaration_specifiers)
) end
)
 in (LrTable.NT 19,(result,function_specifiers1left,
declaration_specifiers1right),rest671) end
| (49,(_,(MlyValue.compound_statement compound_statement1,_,
compound_statement1right))::(_,(MlyValue.declarator declarator1,_,
declaratorright))::(_,(MlyValue.declaration_specifiers 
declaration_specifiers1,declaration_specifiersleft as 
declaration_specifiers1left,_))::rest671) => let val result=
MlyValue.function_definition(fn _ => let val declaration_specifiers
 as declaration_specifiers1=declaration_specifiers1 ()
val declarator as declarator1=declarator1 ()
val compound_statement as compound_statement1=compound_statement1 ()
 in (
let val basetype = extract_type ctxt declaration_specifiers
             val fnspecs = extract_fnspecs (node declaration_specifiers)
             val _ =
                 case has_typedef declaration_specifiers of
                   NONE => ()
                 | SOME (l,r) =>
                    errorStr' ctxt (l, r, "Typedef illegal in function def")
             val (nm, ad, params0, attrs) = node declarator
             val params =
                 case params0 of
                   NONE => (errorStr' ctxt (left declarator,
                                      right declarator,
                                      "Function def with no params!");
                            [])
                 | SOME ps => check_names ctxt (node nm) ps
             val rettype = case (node ad) (node basetype) of
                             Function(retty, _) => retty
                           | _ => (errorStr' ctxt (left declarator,
                                             right compound_statement,
                                             "Attempted fn def with bad \
                                             \declarator");
                                   node basetype)
             val fnspecs = merge_specs [gcc_attribs attrs] fnspecs
         in
           if List.exists (fn fs => fs = didnt_translate) fnspecs then
             Decl (wrap(ExtFnDecl{rettype = rettype,
                                  params = unwrap_params params0,
                                  name = nm,
                                  specs = fnspecs},
                        declaration_specifiersleft,
                        declaratorright))
           else
             FnDefn((rettype, nm), params, fnspecs, compound_statement)
         end
) end
)
 in (LrTable.NT 39,(result,declaration_specifiers1left,
compound_statement1right),rest671) end
| (50,rest671) => let val result=MlyValue.parameter_list(fn _ => (
wrap([], defaultPos, defaultPos)))
 in (LrTable.NT 37,(result,defaultPos,defaultPos),rest671) end
| (51,(_,(MlyValue.parameter_list1 parameter_list11,
parameter_list11left,parameter_list11right))::rest671) => let val 
result=MlyValue.parameter_list(fn _ => let val parameter_list1 as 
parameter_list11=parameter_list11 ()
 in (parameter_list1) end
)
 in (LrTable.NT 37,(result,parameter_list11left,parameter_list11right)
,rest671) end
| (52,(_,(MlyValue.parameter_declaration parameter_declaration1,
parameter_declaration1left,parameter_declaration1right))::rest671) => 
let val result=MlyValue.parameter_list1(fn _ => let val 
parameter_declaration as parameter_declaration1=parameter_declaration1
 ()
 in (
wrap([parameter_declaration], left parameter_declaration,
                      right parameter_declaration)
) end
)
 in (LrTable.NT 38,(result,parameter_declaration1left,
parameter_declaration1right),rest671) end
| (53,(_,(MlyValue.parameter_list1 parameter_list11,_,
parameter_list11right))::_::(_,(MlyValue.parameter_declaration 
parameter_declaration1,parameter_declaration1left,_))::rest671) => 
let val result=MlyValue.parameter_list1(fn _ => let val 
parameter_declaration as parameter_declaration1=parameter_declaration1
 ()
val parameter_list1 as parameter_list11=parameter_list11 ()
 in (
wrap(parameter_declaration :: node parameter_list1,
                      left parameter_declaration, right parameter_list1)
) end
)
 in (LrTable.NT 38,(result,parameter_declaration1left,
parameter_list11right),rest671) end
| (54,(_,(MlyValue.declarator declarator1,_,declarator1right))::(_,(
MlyValue.declaration_specifiers declaration_specifiers1,
declaration_specifiers1left,_))::rest671) => let val result=
MlyValue.parameter_declaration(fn _ => let val declaration_specifiers
 as declaration_specifiers1=declaration_specifiers1 ()
val declarator as declarator1=declarator1 ()
 in (
let val basety = extract_type ctxt declaration_specifiers
                     val _ = wonky_pdec_check ctxt declaration_specifiers
                     val (nm, a, _, _) = node declarator
                 in
                   wrap((node a (node basety), SOME nm),
                        left declaration_specifiers,
                        right declarator)
                 end
) end
)
 in (LrTable.NT 36,(result,declaration_specifiers1left,
declarator1right),rest671) end
| (55,(_,(MlyValue.abstract_declarator abstract_declarator1,_,
abstract_declarator1right))::(_,(MlyValue.declaration_specifiers 
declaration_specifiers1,declaration_specifiers1left,_))::rest671) => 
let val result=MlyValue.parameter_declaration(fn _ => let val 
declaration_specifiers as declaration_specifiers1=
declaration_specifiers1 ()
val abstract_declarator as abstract_declarator1=abstract_declarator1 
()
 in (
let val basety = extract_type ctxt declaration_specifiers
                     val _ = wonky_pdec_check ctxt declaration_specifiers
                     val a = node abstract_declarator
                 in
                   wrap((a (node basety), NONE),
                        left declaration_specifiers,
                        right abstract_declarator)
                 end
) end
)
 in (LrTable.NT 36,(result,declaration_specifiers1left,
abstract_declarator1right),rest671) end
| (56,(_,(MlyValue.declaration_specifiers declaration_specifiers1,
declaration_specifiers1left,declaration_specifiers1right))::rest671)
 => let val result=MlyValue.parameter_declaration(fn _ => let val 
declaration_specifiers as declaration_specifiers1=
declaration_specifiers1 ()
 in (
let val basety = extract_type ctxt declaration_specifiers
                     val _ = wonky_pdec_check ctxt declaration_specifiers
                 in
                   wrap((node basety, NONE),
                        left declaration_specifiers,
                        right declaration_specifiers)
                 end
) end
)
 in (LrTable.NT 36,(result,declaration_specifiers1left,
declaration_specifiers1right),rest671) end
| (57,(_,(_,_,RCURLYright as RCURLY1right))::(_,(
MlyValue.block_item_list block_item_list1,_,_))::(_,(_,LCURLYleft as 
LCURLY1left,_))::rest671) => let val result=
MlyValue.compound_statement(fn _ => let val block_item_list as 
block_item_list1=block_item_list1 ()
 in (wrap(block_item_list, LCURLYleft, RCURLYright)) end
)
 in (LrTable.NT 40,(result,LCURLY1left,RCURLY1right),rest671) end
| (58,rest671) => let val result=MlyValue.block_item_list(fn _ => ([])
)
 in (LrTable.NT 34,(result,defaultPos,defaultPos),rest671) end
| (59,(_,(MlyValue.block_item_list block_item_list1,_,
block_item_list1right))::(_,(MlyValue.block_item block_item1,
block_item1left,_))::rest671) => let val result=
MlyValue.block_item_list(fn _ => let val block_item as block_item1=
block_item1 ()
val block_item_list as block_item_list1=block_item_list1 ()
 in (block_item @ block_item_list) end
)
 in (LrTable.NT 34,(result,block_item1left,block_item_list1right),
rest671) end
| (60,(_,(MlyValue.declaration declaration1,declaration1left,
declaration1right))::rest671) => let val result=MlyValue.block_item(
fn _ => let val declaration as declaration1=declaration1 ()
 in (map BI_Decl declaration) end
)
 in (LrTable.NT 35,(result,declaration1left,declaration1right),rest671
) end
| (61,(_,(MlyValue.statement statement1,statement1left,statement1right
))::rest671) => let val result=MlyValue.block_item(fn _ => let val 
statement as statement1=statement1 ()
 in ([BI_Stmt statement]) end
)
 in (LrTable.NT 35,(result,statement1left,statement1right),rest671)
 end
| (62,rest671) => let val result=MlyValue.statement_list(fn _ => ([]))
 in (LrTable.NT 42,(result,defaultPos,defaultPos),rest671) end
| (63,(_,(MlyValue.statement_list1 statement_list11,
statement_list11left,statement_list11right))::rest671) => let val 
result=MlyValue.statement_list(fn _ => let val statement_list1 as 
statement_list11=statement_list11 ()
 in (statement_list1) end
)
 in (LrTable.NT 42,(result,statement_list11left,statement_list11right)
,rest671) end
| (64,(_,(MlyValue.statement statement1,statement1left,statement1right
))::rest671) => let val result=MlyValue.statement_list1(fn _ => let 
val statement as statement1=statement1 ()
 in ([statement]) end
)
 in (LrTable.NT 43,(result,statement1left,statement1right),rest671)
 end
| (65,(_,(MlyValue.statement_list1 statement_list11,_,
statement_list11right))::(_,(MlyValue.statement statement1,
statement1left,_))::rest671) => let val result=
MlyValue.statement_list1(fn _ => let val statement as statement1=
statement1 ()
val statement_list1 as statement_list11=statement_list11 ()
 in (statement::statement_list1) end
)
 in (LrTable.NT 43,(result,statement1left,statement_list11right),
rest671) end
| (66,(_,(MlyValue.struct_declaration struct_declaration1,
struct_declaration1left,struct_declaration1right))::rest671) => let 
val result=MlyValue.struct_declaration_list(fn _ => let val 
struct_declaration as struct_declaration1=struct_declaration1 ()
 in (struct_declaration) end
)
 in (LrTable.NT 28,(result,struct_declaration1left,
struct_declaration1right),rest671) end
| (67,(_,(MlyValue.struct_declaration_list struct_declaration_list1,_,
struct_declaration_list1right))::(_,(MlyValue.struct_declaration 
struct_declaration1,struct_declaration1left,_))::rest671) => let val 
result=MlyValue.struct_declaration_list(fn _ => let val 
struct_declaration as struct_declaration1=struct_declaration1 ()
val struct_declaration_list as struct_declaration_list1=
struct_declaration_list1 ()
 in (
let val (sflds1, siddecls1) = struct_declaration
                     val (sflds2, siddecls2) = struct_declaration_list
                 in
                   (wrap(node sflds1 @ node sflds2, left sflds1, right sflds2),
                    siddecls1 @ siddecls2)
                 end
) end
)
 in (LrTable.NT 28,(result,struct_declaration1left,
struct_declaration_list1right),rest671) end
| (68,(_,(MlyValue.type_specifier type_specifier1,type_specifier1left,
type_specifier1right))::rest671) => let val result=
MlyValue.specifier_qualifier_list(fn _ => let val type_specifier as 
type_specifier1=type_specifier1 ()
 in (
wrap([TypeSpec type_specifier],
                      tsleft type_specifier,
                      tsright type_specifier)
) end
)
 in (LrTable.NT 20,(result,type_specifier1left,type_specifier1right),
rest671) end
| (69,(_,(MlyValue.specifier_qualifier_list specifier_qualifier_list1,
_,specifier_qualifier_list1right))::(_,(MlyValue.type_specifier 
type_specifier1,type_specifier1left,_))::rest671) => let val result=
MlyValue.specifier_qualifier_list(fn _ => let val type_specifier as 
type_specifier1=type_specifier1 ()
val specifier_qualifier_list as specifier_qualifier_list1=
specifier_qualifier_list1 ()
 in (
wrap(TypeSpec type_specifier :: node specifier_qualifier_list,
                      tsleft type_specifier, right specifier_qualifier_list)
) end
)
 in (LrTable.NT 20,(result,type_specifier1left,
specifier_qualifier_list1right),rest671) end
| (70,(_,(MlyValue.type_qualifier type_qualifier1,type_qualifier1left,
type_qualifier1right))::rest671) => let val result=
MlyValue.specifier_qualifier_list(fn _ => let val type_qualifier as 
type_qualifier1=type_qualifier1 ()
 in (
wrap([TypeQual type_qualifier],
                      left type_qualifier, right type_qualifier)
) end
)
 in (LrTable.NT 20,(result,type_qualifier1left,type_qualifier1right),
rest671) end
| (71,(_,(MlyValue.specifier_qualifier_list specifier_qualifier_list1,
_,specifier_qualifier_list1right))::(_,(MlyValue.type_qualifier 
type_qualifier1,type_qualifier1left,_))::rest671) => let val result=
MlyValue.specifier_qualifier_list(fn _ => let val type_qualifier as 
type_qualifier1=type_qualifier1 ()
val specifier_qualifier_list as specifier_qualifier_list1=
specifier_qualifier_list1 ()
 in (
wrap(TypeQual type_qualifier :: node specifier_qualifier_list,
                      left type_qualifier, right specifier_qualifier_list)
) end
)
 in (LrTable.NT 20,(result,type_qualifier1left,
specifier_qualifier_list1right),rest671) end
| (72,(_,(_,CONSTleft as CONST1left,CONSTright as CONST1right))::
rest671) => let val result=MlyValue.type_qualifier(fn _ => (
wrap(Const, CONSTleft, CONSTright)))
 in (LrTable.NT 9,(result,CONST1left,CONST1right),rest671) end
| (73,(_,(_,VOLATILEleft as VOLATILE1left,VOLATILEright as 
VOLATILE1right))::rest671) => let val result=MlyValue.type_qualifier(
fn _ => (wrap(Volatile, VOLATILEleft, VOLATILEright)))
 in (LrTable.NT 9,(result,VOLATILE1left,VOLATILE1right),rest671) end
| (74,(_,(_,RESTRICTleft as RESTRICT1left,RESTRICTright as 
RESTRICT1right))::rest671) => let val result=MlyValue.type_qualifier(
fn _ => (wrap(Restrict, RESTRICTleft, RESTRICTright)))
 in (LrTable.NT 9,(result,RESTRICT1left,RESTRICT1right),rest671) end
| (75,(_,(MlyValue.type_qualifier type_qualifier1,type_qualifier1left,
type_qualifier1right))::rest671) => let val result=
MlyValue.type_qualifier_list(fn _ => let val type_qualifier as 
type_qualifier1=type_qualifier1 ()
 in ([type_qualifier]) end
)
 in (LrTable.NT 10,(result,type_qualifier1left,type_qualifier1right),
rest671) end
| (76,(_,(MlyValue.type_qualifier_list type_qualifier_list1,_,
type_qualifier_list1right))::(_,(MlyValue.type_qualifier 
type_qualifier1,type_qualifier1left,_))::rest671) => let val result=
MlyValue.type_qualifier_list(fn _ => let val type_qualifier as 
type_qualifier1=type_qualifier1 ()
val type_qualifier_list as type_qualifier_list1=type_qualifier_list1 
()
 in (type_qualifier::type_qualifier_list) end
)
 in (LrTable.NT 10,(result,type_qualifier1left,
type_qualifier_list1right),rest671) end
| (77,(_,(_,_,YSEMI1right))::(_,(MlyValue.struct_declarator_list 
struct_declarator_list1,_,_))::(_,(MlyValue.specifier_qualifier_list 
specifier_qualifier_list1,specifier_qualifier_list1left,_))::rest671)
 => let val result=MlyValue.struct_declaration(fn _ => let val 
specifier_qualifier_list as specifier_qualifier_list1=
specifier_qualifier_list1 ()
val struct_declarator_list as struct_declarator_list1=
struct_declarator_list1 ()
 in (
let val basetype = extract_type ctxt specifier_qualifier_list
                     val sdecls = first_sdecls (node specifier_qualifier_list)
                     val _ = case first_enum_dec (node specifier_qualifier_list) of
                               NONE => ()
                             | SOME es => errorStr' ctxt (left es, right es,
                                                    "Don't declare enumerations\
                                                    \ inside structs")
                     fun apply_decltor sd = let
                       val (ddw, eop) = sd
                       val (nm,ad,_,attrs) = node ddw
                     in
                       (node ad (node basetype), apnode C_field_name nm, eop, attrs)
                     end
                 in
                   (wrap(map apply_decltor (node struct_declarator_list),
                         left basetype, right struct_declarator_list),
                    sdecls)
                 end
) end
)
 in (LrTable.NT 29,(result,specifier_qualifier_list1left,YSEMI1right),
rest671) end
| (78,(_,(MlyValue.struct_declarator struct_declarator1,
struct_declarator1left,struct_declarator1right))::rest671) => let val 
result=MlyValue.struct_declarator_list(fn _ => let val 
struct_declarator as struct_declarator1=struct_declarator1 ()
 in (
wrap ([node struct_declarator], left struct_declarator,
                            right struct_declarator)
) end
)
 in (LrTable.NT 63,(result,struct_declarator1left,
struct_declarator1right),rest671) end
| (79,(_,(MlyValue.struct_declarator_list struct_declarator_list1,_,
struct_declarator_list1right))::_::(_,(MlyValue.struct_declarator 
struct_declarator1,struct_declarator1left,_))::rest671) => let val 
result=MlyValue.struct_declarator_list(fn _ => let val 
struct_declarator as struct_declarator1=struct_declarator1 ()
val struct_declarator_list as struct_declarator_list1=
struct_declarator_list1 ()
 in (
wrap (node struct_declarator::node struct_declarator_list,
                       left struct_declarator, right struct_declarator_list)
) end
)
 in (LrTable.NT 63,(result,struct_declarator1left,
struct_declarator_list1right),rest671) end
| (80,(_,(MlyValue.declarator declarator1,declarator1left,
declarator1right))::rest671) => let val result=
MlyValue.struct_declarator(fn _ => let val declarator as declarator1=
declarator1 ()
 in (wrap((declarator, NONE), left declarator, right declarator)) end
)
 in (LrTable.NT 62,(result,declarator1left,declarator1right),rest671)
 end
| (81,(_,(MlyValue.rexpression rexpression1,_,rexpression1right))::_::
(_,(MlyValue.declarator declarator1,declarator1left,_))::rest671) => 
let val result=MlyValue.struct_declarator(fn _ => let val declarator
 as declarator1=declarator1 ()
val rexpression as rexpression1=rexpression1 ()
 in (
wrap((declarator, SOME rexpression), left declarator,
                      eright rexpression)
) end
)
 in (LrTable.NT 62,(result,declarator1left,rexpression1right),rest671)
 end
| (82,(_,(MlyValue.init_declarator init_declarator1,
init_declarator1left,init_declarator1right))::rest671) => let val 
result=MlyValue.init_declarator_list(fn _ => let val init_declarator
 as init_declarator1=init_declarator1 ()
 in ([init_declarator]) end
)
 in (LrTable.NT 65,(result,init_declarator1left,init_declarator1right)
,rest671) end
| (83,(_,(MlyValue.init_declarator_list init_declarator_list1,_,
init_declarator_list1right))::_::(_,(MlyValue.init_declarator 
init_declarator1,init_declarator1left,_))::rest671) => let val result=
MlyValue.init_declarator_list(fn _ => let val init_declarator as 
init_declarator1=init_declarator1 ()
val init_declarator_list as init_declarator_list1=
init_declarator_list1 ()
 in (init_declarator :: init_declarator_list) end
)
 in (LrTable.NT 65,(result,init_declarator1left,
init_declarator_list1right),rest671) end
| (84,(_,(MlyValue.declarator declarator1,declarator1left,
declarator1right))::rest671) => let val result=
MlyValue.init_declarator(fn _ => let val declarator as declarator1=
declarator1 ()
 in (wrap((declarator, NONE), left declarator, right declarator)) end
)
 in (LrTable.NT 64,(result,declarator1left,declarator1right),rest671)
 end
| (85,(_,(MlyValue.initializer initializer1,_,initializer1right))::_::
(_,(MlyValue.declarator declarator1,declarator1left,_))::rest671) => 
let val result=MlyValue.init_declarator(fn _ => let val declarator as 
declarator1=declarator1 ()
val initializer as initializer1=initializer1 ()
 in (
wrap((declarator, SOME (node initializer)),
                      left declarator, right initializer)
) end
)
 in (LrTable.NT 64,(result,declarator1left,initializer1right),rest671)
 end
| (86,(_,(_,YSTARleft as YSTAR1left,YSTARright as YSTAR1right))::
rest671) => let val result=MlyValue.pointer(fn _ => (
ptrdecl YSTARleft YSTARright))
 in (LrTable.NT 58,(result,YSTAR1left,YSTAR1right),rest671) end
| (87,(_,(MlyValue.type_qualifier_list type_qualifier_list1,_,
type_qualifier_list1right))::(_,(_,YSTARleft as YSTAR1left,_))::
rest671) => let val result=MlyValue.pointer(fn _ => let val 
type_qualifier_list as type_qualifier_list1=type_qualifier_list1 ()
 in (ptrdecl YSTARleft (right (List.last type_qualifier_list))) end
)
 in (LrTable.NT 58,(result,YSTAR1left,type_qualifier_list1right),
rest671) end
| (88,(_,(MlyValue.pointer pointer1,_,pointer1right))::(_,(_,YSTARleft
 as YSTAR1left,YSTARright))::rest671) => let val result=
MlyValue.pointer(fn _ => let val pointer as pointer1=pointer1 ()
 in (ooa(ptrdecl YSTARleft YSTARright, pointer)) end
)
 in (LrTable.NT 58,(result,YSTAR1left,pointer1right),rest671) end
| (89,(_,(MlyValue.pointer pointer1,_,pointer1right))::(_,(
MlyValue.type_qualifier_list type_qualifier_list1,_,_))::(_,(_,
YSTARleft as YSTAR1left,_))::rest671) => let val result=
MlyValue.pointer(fn _ => let val type_qualifier_list as 
type_qualifier_list1=type_qualifier_list1 ()
val pointer as pointer1=pointer1 ()
 in (
ooa(ptrdecl YSTARleft (right (List.last type_qualifier_list)),
                     pointer)
) end
)
 in (LrTable.NT 58,(result,YSTAR1left,pointer1right),rest671) end
| (90,(_,(MlyValue.direct_declarator direct_declarator1,_,
direct_declarator1right))::(_,(MlyValue.pointer pointer1,pointer1left,
_))::rest671) => let val result=MlyValue.declarator(fn _ => let val 
pointer as pointer1=pointer1 ()
val direct_declarator as direct_declarator1=direct_declarator1 ()
 in (ood(direct_declarator, pointer)) end
)
 in (LrTable.NT 59,(result,pointer1left,direct_declarator1right),
rest671) end
| (91,(_,(MlyValue.direct_declarator direct_declarator1,_,
direct_declarator1right))::(_,(MlyValue.attribute_specifier 
attribute_specifier1,_,_))::(_,(MlyValue.pointer pointer1,pointer1left
,_))::rest671) => let val result=MlyValue.declarator(fn _ => let val 
pointer as pointer1=pointer1 ()
val attribute_specifier as attribute_specifier1=attribute_specifier1 
()
val direct_declarator as direct_declarator1=direct_declarator1 ()
 in (
ood(add_attributes(direct_declarator,
                                    node attribute_specifier),
                     pointer)
) end
)
 in (LrTable.NT 59,(result,pointer1left,direct_declarator1right),
rest671) end
| (92,(_,(MlyValue.direct_declarator direct_declarator1,
direct_declarator1left,direct_declarator1right))::rest671) => let val 
result=MlyValue.declarator(fn _ => let val direct_declarator as 
direct_declarator1=direct_declarator1 ()
 in (direct_declarator) end
)
 in (LrTable.NT 59,(result,direct_declarator1left,
direct_declarator1right),rest671) end
| (93,(_,(_,_,SPEC_BLOCKEND1right))::(_,(MlyValue.idlist idlist1,_,_))
::(_,(_,CALLS1left,_))::rest671) => let val result=
MlyValue.calls_block(fn _ => let val idlist as idlist1=idlist1 ()
 in (SOME idlist) end
)
 in (LrTable.NT 105,(result,CALLS1left,SPEC_BLOCKEND1right),rest671)
 end
| (94,rest671) => let val result=MlyValue.calls_block(fn _ => (NONE))
 in (LrTable.NT 105,(result,defaultPos,defaultPos),rest671) end
| (95,(_,(MlyValue.ID ID1,IDleft as ID1left,IDright as ID1right))::
rest671) => let val result=MlyValue.direct_declarator(fn _ => let val 
ID as ID1=ID1 ()
 in (
wrap((wrap(ID, IDleft, IDright),
                       wrap((fn t => t), IDleft, IDright),
                       NONE,
                       []),
                      IDleft, IDright)
) end
)
 in (LrTable.NT 66,(result,ID1left,ID1right),rest671) end
| (96,(_,(_,_,RBRACKETright as RBRACKET1right))::(_,(
MlyValue.rexpression rexpression1,_,_))::(_,(_,LBRACKETleft,_))::(_,(
MlyValue.direct_declarator direct_declarator1,direct_declarator1left,_
))::rest671) => let val result=MlyValue.direct_declarator(fn _ => let 
val direct_declarator as direct_declarator1=direct_declarator1 ()
val rexpression as rexpression1=rexpression1 ()
 in (
ood(direct_declarator,
                     arraydecl LBRACKETleft RBRACKETright (SOME rexpression))
) end
)
 in (LrTable.NT 66,(result,direct_declarator1left,RBRACKET1right),
rest671) end
| (97,(_,(_,_,RBRACKETright as RBRACKET1right))::(_,(_,LBRACKETleft,_)
)::(_,(MlyValue.direct_declarator direct_declarator1,
direct_declarator1left,_))::rest671) => let val result=
MlyValue.direct_declarator(fn _ => let val direct_declarator as 
direct_declarator1=direct_declarator1 ()
 in (
ood(direct_declarator,
                     arraydecl LBRACKETleft RBRACKETright NONE)
) end
)
 in (LrTable.NT 66,(result,direct_declarator1left,RBRACKET1right),
rest671) end
| (98,(_,(_,_,RPARENright as RPAREN1right))::(_,(MlyValue.declarator 
declarator1,_,_))::(_,(_,LPARENleft as LPAREN1left,_))::rest671) => 
let val result=MlyValue.direct_declarator(fn _ => let val declarator
 as declarator1=declarator1 ()
 in (wrap(node declarator, LPARENleft, RPARENright)) end
)
 in (LrTable.NT 66,(result,LPAREN1left,RPAREN1right),rest671) end
| (99,(_,(MlyValue.calls_block calls_block1,_,calls_block1right))::_::
(_,(MlyValue.parameter_list parameter_list1,_,_))::_::(_,(
MlyValue.direct_declarator direct_declarator1,direct_declarator1left,_
))::rest671) => let val result=MlyValue.direct_declarator(fn _ => let 
val direct_declarator as direct_declarator1=direct_declarator1 ()
val parameter_list as parameter_list1=parameter_list1 ()
val calls_block1=calls_block1 ()
 in (
let val ps = check_params ctxt parameter_list
                 in
                   addparams(ood(direct_declarator,
                                 fndecl (left direct_declarator)
                                        (right direct_declarator)
                                        (map (#1 o node) ps)),
                             ps)
                 end
) end
)
 in (LrTable.NT 66,(result,direct_declarator1left,calls_block1right),
rest671) end
| (100,(_,(MlyValue.attribute_specifier attribute_specifier1,_,
attribute_specifier1right))::(_,(MlyValue.direct_declarator 
direct_declarator1,direct_declarator1left,_))::rest671) => let val 
result=MlyValue.direct_declarator(fn _ => let val direct_declarator
 as direct_declarator1=direct_declarator1 ()
val attribute_specifier as attribute_specifier1=attribute_specifier1 
()
 in (
add_attributes(direct_declarator,
                                node attribute_specifier)
) end
)
 in (LrTable.NT 66,(result,direct_declarator1left,
attribute_specifier1right),rest671) end
| (101,(_,(MlyValue.asm_declarator_mod asm_declarator_mod1,_,
asm_declarator_mod1right))::(_,(MlyValue.direct_declarator 
direct_declarator1,direct_declarator1left,_))::rest671) => let val 
result=MlyValue.direct_declarator(fn _ => let val direct_declarator
 as direct_declarator1=direct_declarator1 ()
val asm_declarator_mod1=asm_declarator_mod1 ()
 in (direct_declarator) end
)
 in (LrTable.NT 66,(result,direct_declarator1left,
asm_declarator_mod1right),rest671) end
| (102,(_,(_,_,RPAREN1right))::(_,(MlyValue.cstring_literal 
cstring_literal1,_,_))::_::(_,(_,YASM1left,_))::rest671) => let val 
result=MlyValue.asm_declarator_mod(fn _ => let val cstring_literal1=
cstring_literal1 ()
 in (()) end
)
 in (LrTable.NT 67,(result,YASM1left,RPAREN1right),rest671) end
| (103,(_,(MlyValue.ID ID1,IDleft as ID1left,IDright as ID1right))::
rest671) => let val result=MlyValue.struct_id(fn _ => let val ID as 
ID1=ID1 ()
 in (wrap(ID, IDleft, IDright)) end
)
 in (LrTable.NT 70,(result,ID1left,ID1right),rest671) end
| (104,(_,(MlyValue.TYPEID TYPEID1,TYPEIDleft as TYPEID1left,
TYPEIDright as TYPEID1right))::rest671) => let val result=
MlyValue.struct_id(fn _ => let val TYPEID as TYPEID1=TYPEID1 ()
 in (wrap(TYPEID, TYPEIDleft, TYPEIDright)) end
)
 in (LrTable.NT 70,(result,TYPEID1left,TYPEID1right),rest671) end
| (105,(_,(MlyValue.struct_id struct_id1,_,struct_id1right))::(_,(_,
STRUCTleft as STRUCT1left,_))::rest671) => let val result=
MlyValue.struct_or_union_specifier(fn _ => let val struct_id as 
struct_id1=struct_id1 ()
 in (
(wrap(StructTy
                           (C_struct_name (node struct_id)),
                       STRUCTleft,
                       right struct_id),
                  [])
) end
)
 in (LrTable.NT 69,(result,STRUCT1left,struct_id1right),rest671) end
| (106,(_,(_,_,RCURLYright as RCURLY1right))::(_,(
MlyValue.struct_declaration_list struct_declaration_list1,_,_))::_::(_
,(MlyValue.struct_id struct_id1,_,_))::(_,(_,STRUCTleft as STRUCT1left
,_))::rest671) => let val result=MlyValue.struct_or_union_specifier(
fn _ => let val struct_id as struct_id1=struct_id1 ()
val struct_declaration_list as struct_declaration_list1=
struct_declaration_list1 ()
 in (
let val (flds, decls) = struct_declaration_list
                     val raw_s_name = node struct_id
                     val munged_name = C_struct_name raw_s_name
                     val sname_w = wrap(munged_name, left struct_id,
                                        right struct_id)
                 in
                   (wrap(StructTy munged_name, STRUCTleft, right struct_id),
                    wrap((sname_w, node flds, bogwrap []),
                         STRUCTleft, RCURLYright) :: decls)
                 end
) end
)
 in (LrTable.NT 69,(result,STRUCT1left,RCURLY1right),rest671) end
| (107,(_,(MlyValue.attribute_specifier attribute_specifier1,_,
attribute_specifier1right))::(_,(_,_,RCURLYright))::(_,(
MlyValue.struct_declaration_list struct_declaration_list1,_,_))::_::(_
,(MlyValue.struct_id struct_id1,_,_))::(_,(_,STRUCTleft as STRUCT1left
,_))::rest671) => let val result=MlyValue.struct_or_union_specifier(
fn _ => let val struct_id as struct_id1=struct_id1 ()
val struct_declaration_list as struct_declaration_list1=
struct_declaration_list1 ()
val attribute_specifier as attribute_specifier1=attribute_specifier1 
()
 in (
let val (flds, decls) = struct_declaration_list
                     val raw_s_name = node struct_id
                     val munged_name = C_struct_name raw_s_name
                     val sname_w = wrap(munged_name, left struct_id,
                                        right struct_id)
                 in
                   (wrap(StructTy munged_name, STRUCTleft, right struct_id),
                    wrap((sname_w, node flds, attribute_specifier),
                         STRUCTleft, RCURLYright) :: decls)
                 end
) end
)
 in (LrTable.NT 69,(result,STRUCT1left,attribute_specifier1right),
rest671) end
| (108,(_,(_,_,RCURLYright as RCURLY1right))::(_,(
MlyValue.struct_declaration_list struct_declaration_list1,_,_))::(_,(_
,LCURLYleft,_))::(_,(_,STRUCTleft as STRUCT1left,STRUCTright))::
rest671) => let val result=MlyValue.struct_or_union_specifier(fn _ => 
let val struct_declaration_list as struct_declaration_list1=
struct_declaration_list1 ()
 in (
let
                   val (flds, decls) = struct_declaration_list
                   val anonid = gen_struct_id ()
                   val anonw = wrap(anonid, STRUCTright, LCURLYleft)
                 in
                   (wrap(StructTy anonid, STRUCTleft, LCURLYleft),
                    wrap((anonw, node flds, bogwrap []), STRUCTleft, RCURLYright) ::
                    decls)
                 end
) end
)
 in (LrTable.NT 69,(result,STRUCT1left,RCURLY1right),rest671) end
| (109,(_,(MlyValue.attribute_specifier attribute_specifier1,_,
attribute_specifier1right))::(_,(_,_,RCURLYright))::(_,(
MlyValue.struct_declaration_list struct_declaration_list1,_,_))::(_,(_
,LCURLYleft,_))::(_,(_,STRUCTleft as STRUCT1left,STRUCTright))::
rest671) => let val result=MlyValue.struct_or_union_specifier(fn _ => 
let val struct_declaration_list as struct_declaration_list1=
struct_declaration_list1 ()
val attribute_specifier as attribute_specifier1=attribute_specifier1 
()
 in (
let
                   val (flds, decls) = struct_declaration_list
                   val anonid = gen_struct_id ()
                   val anonw = wrap(anonid, STRUCTright, LCURLYleft)
                 in
                   (wrap(StructTy anonid, STRUCTleft, LCURLYleft),
                    wrap((anonw, node flds, attribute_specifier), STRUCTleft, RCURLYright) ::
                    decls)
                 end
) end
)
 in (LrTable.NT 69,(result,STRUCT1left,attribute_specifier1right),
rest671) end
| (110,(_,(MlyValue.struct_id struct_id1,_,struct_id1right))::(_,(_,
UNIONleft as UNION1left,_))::rest671) => let val result=
MlyValue.struct_or_union_specifier(fn _ => let val struct_id as 
struct_id1=struct_id1 ()
 in (
(wrap(UnionTy
                           (C_struct_name (node struct_id)),
                       UNIONleft,
                       right struct_id),
                  [])
) end
)
 in (LrTable.NT 69,(result,UNION1left,struct_id1right),rest671) end
| (111,(_,(_,_,RCURLYright as RCURLY1right))::(_,(
MlyValue.struct_declaration_list struct_declaration_list1,_,_))::_::(_
,(MlyValue.struct_id struct_id1,_,_))::(_,(_,UNIONleft as UNION1left,_
))::rest671) => let val result=MlyValue.struct_or_union_specifier(fn _
 => let val struct_id as struct_id1=struct_id1 ()
val struct_declaration_list as struct_declaration_list1=
struct_declaration_list1 ()
 in (
let val (flds, decls) = struct_declaration_list
                     val raw_s_name = node struct_id
                     val munged_name = C_struct_name raw_s_name
                     val sname_w = wrap(munged_name, left struct_id,
                                        right struct_id)
                 in
                   (wrap(UnionTy munged_name, UNIONleft, right struct_id),
                    wrap((sname_w, node flds, bogwrap []),
                         UNIONleft, RCURLYright) :: decls)
                 end
) end
)
 in (LrTable.NT 69,(result,UNION1left,RCURLY1right),rest671) end
| (112,(_,(MlyValue.attribute_specifier attribute_specifier1,_,
attribute_specifier1right))::(_,(_,_,RCURLYright))::(_,(
MlyValue.struct_declaration_list struct_declaration_list1,_,_))::_::(_
,(MlyValue.struct_id struct_id1,_,_))::(_,(_,UNIONleft as UNION1left,_
))::rest671) => let val result=MlyValue.struct_or_union_specifier(fn _
 => let val struct_id as struct_id1=struct_id1 ()
val struct_declaration_list as struct_declaration_list1=
struct_declaration_list1 ()
val attribute_specifier as attribute_specifier1=attribute_specifier1 
()
 in (
let val (flds, decls) = struct_declaration_list
                     val raw_s_name = node struct_id
                     val munged_name = C_struct_name raw_s_name
                     val sname_w = wrap(munged_name, left struct_id,
                                        right struct_id)
                 in
                   (wrap(UnionTy munged_name, UNIONleft, right struct_id),
                    wrap((sname_w, node flds, attribute_specifier),
                         UNIONleft, RCURLYright) :: decls)
                 end
) end
)
 in (LrTable.NT 69,(result,UNION1left,attribute_specifier1right),
rest671) end
| (113,(_,(_,_,RCURLYright as RCURLY1right))::(_,(
MlyValue.struct_declaration_list struct_declaration_list1,_,_))::(_,(_
,LCURLYleft,_))::(_,(_,UNIONleft as UNION1left,UNIONright))::rest671)
 => let val result=MlyValue.struct_or_union_specifier(fn _ => let val 
struct_declaration_list as struct_declaration_list1=
struct_declaration_list1 ()
 in (
let
                   val (flds, decls) = struct_declaration_list
                   val anonid = gen_struct_id ()
                   val anonw = wrap(anonid, UNIONright, LCURLYleft)
                 in
                   (wrap(UnionTy anonid, UNIONleft, LCURLYleft),
                    wrap((anonw, node flds, bogwrap []), UNIONleft, RCURLYright) ::
                    decls)
                 end
) end
)
 in (LrTable.NT 69,(result,UNION1left,RCURLY1right),rest671) end
| (114,(_,(MlyValue.attribute_specifier attribute_specifier1,_,
attribute_specifier1right))::(_,(_,_,RCURLYright))::(_,(
MlyValue.struct_declaration_list struct_declaration_list1,_,_))::(_,(_
,LCURLYleft,_))::(_,(_,UNIONleft as UNION1left,UNIONright))::rest671)
 => let val result=MlyValue.struct_or_union_specifier(fn _ => let val 
struct_declaration_list as struct_declaration_list1=
struct_declaration_list1 ()
val attribute_specifier as attribute_specifier1=attribute_specifier1 
()
 in (
let
                   val (flds, decls) = struct_declaration_list
                   val anonid = gen_struct_id ()
                   val anonw = wrap(anonid, UNIONright, LCURLYleft)
                 in
                   (wrap(UnionTy anonid, UNIONleft, LCURLYleft),
                    wrap((anonw, node flds, attribute_specifier), UNIONleft, RCURLYright) ::
                    decls)
                 end
) end
)
 in (LrTable.NT 69,(result,UNION1left,attribute_specifier1right),
rest671) end
| (115,(_,(_,INTleft as INT1left,INTright as INT1right))::rest671) => 
let val result=MlyValue.type_specifier(fn _ => (
Tstok(wrap(ts_int, INTleft, INTright))))
 in (LrTable.NT 68,(result,INT1left,INT1right),rest671) end
| (116,(_,(_,CHARleft as CHAR1left,CHARright as CHAR1right))::rest671)
 => let val result=MlyValue.type_specifier(fn _ => (
Tstok(wrap(ts_char, CHARleft, CHARright))))
 in (LrTable.NT 68,(result,CHAR1left,CHAR1right),rest671) end
| (117,(_,(_,SHORTleft as SHORT1left,SHORTright as SHORT1right))::
rest671) => let val result=MlyValue.type_specifier(fn _ => (
Tstok(wrap(ts_short, SHORTleft, SHORTright))))
 in (LrTable.NT 68,(result,SHORT1left,SHORT1right),rest671) end
| (118,(_,(_,LONGleft as LONG1left,LONGright as LONG1right))::rest671)
 => let val result=MlyValue.type_specifier(fn _ => (
Tstok(wrap(ts_long, LONGleft, LONGright))))
 in (LrTable.NT 68,(result,LONG1left,LONG1right),rest671) end
| (119,(_,(_,INT128left as INT1281left,INT128right as INT1281right))::
rest671) => let val result=MlyValue.type_specifier(fn _ => (
Tstok(wrap(ts_int128, INT128left, INT128right))))
 in (LrTable.NT 68,(result,INT1281left,INT1281right),rest671) end
| (120,(_,(_,VOIDleft as VOID1left,VOIDright as VOID1right))::rest671)
 => let val result=MlyValue.type_specifier(fn _ => (
Tstok(wrap(ts_void, VOIDleft, VOIDright))))
 in (LrTable.NT 68,(result,VOID1left,VOID1right),rest671) end
| (121,(_,(_,SIGNEDleft as SIGNED1left,SIGNEDright as SIGNED1right))::
rest671) => let val result=MlyValue.type_specifier(fn _ => (
Tstok(wrap(ts_signed, SIGNEDleft, SIGNEDright))))
 in (LrTable.NT 68,(result,SIGNED1left,SIGNED1right),rest671) end
| (122,(_,(_,UNSIGNEDleft as UNSIGNED1left,UNSIGNEDright as 
UNSIGNED1right))::rest671) => let val result=MlyValue.type_specifier(
fn _ => (Tstok(wrap(ts_unsigned, UNSIGNEDleft, UNSIGNEDright))))
 in (LrTable.NT 68,(result,UNSIGNED1left,UNSIGNED1right),rest671) end
| (123,(_,(_,BOOLleft as BOOL1left,BOOLright as BOOL1right))::rest671)
 => let val result=MlyValue.type_specifier(fn _ => (
Tstok(wrap(ts_bool, BOOLleft, BOOLright))))
 in (LrTable.NT 68,(result,BOOL1left,BOOL1right),rest671) end
| (124,(_,(_,_,RPARENright as RPAREN1right))::(_,(MlyValue.rexpression
 rexpression1,_,_))::(_,(_,LPARENleft,_))::(_,(_,YTYPEOF1left,_))::
rest671) => let val result=MlyValue.type_specifier(fn _ => let val 
rexpression as rexpression1=rexpression1 ()
 in (Tstypeof (wrap(rexpression, LPARENleft, RPARENright))) end
)
 in (LrTable.NT 68,(result,YTYPEOF1left,RPAREN1right),rest671) end
| (125,(_,(MlyValue.struct_or_union_specifier 
struct_or_union_specifier1,struct_or_union_specifier1left,
struct_or_union_specifier1right))::rest671) => let val result=
MlyValue.type_specifier(fn _ => let val struct_or_union_specifier as 
struct_or_union_specifier1=struct_or_union_specifier1 ()
 in (Tsstruct (struct_or_union_specifier)) end
)
 in (LrTable.NT 68,(result,struct_or_union_specifier1left,
struct_or_union_specifier1right),rest671) end
| (126,(_,(MlyValue.enum_specifier enum_specifier1,enum_specifier1left
,enum_specifier1right))::rest671) => let val result=
MlyValue.type_specifier(fn _ => let val enum_specifier as 
enum_specifier1=enum_specifier1 ()
 in (Tsenum enum_specifier) end
)
 in (LrTable.NT 68,(result,enum_specifier1left,enum_specifier1right),
rest671) end
| (127,(_,(MlyValue.TYPEID TYPEID1,TYPEIDleft as TYPEID1left,
TYPEIDright as TYPEID1right))::rest671) => let val result=
MlyValue.type_specifier(fn _ => let val TYPEID as TYPEID1=TYPEID1 ()
 in (Tstypeid(wrap(TYPEID, TYPEIDleft, TYPEIDright))) end
)
 in (LrTable.NT 68,(result,TYPEID1left,TYPEID1right),rest671) end
| (128,(_,(_,_,RCURLYright as RCURLY1right))::(_,(
MlyValue.enumerator_list enumerator_list1,_,_))::_::(_,(_,YENUMleft
 as YENUM1left,YENUMright))::rest671) => let val result=
MlyValue.enum_specifier(fn _ => let val enumerator_list as 
enumerator_list1=enumerator_list1 ()
 in (
wrap((wrap(NONE, YENUMleft, YENUMright), enumerator_list),
                      YENUMleft, RCURLYright)
) end
)
 in (LrTable.NT 6,(result,YENUM1left,RCURLY1right),rest671) end
| (129,(_,(_,_,RCURLYright as RCURLY1right))::(_,(
MlyValue.enumerator_list enumerator_list1,_,_))::_::(_,(
MlyValue.struct_id struct_id1,_,_))::(_,(_,YENUMleft as YENUM1left,_))
::rest671) => let val result=MlyValue.enum_specifier(fn _ => let val 
struct_id as struct_id1=struct_id1 ()
val enumerator_list as enumerator_list1=enumerator_list1 ()
 in (
wrap((apnode SOME struct_id, enumerator_list),
                      YENUMleft, RCURLYright)
) end
)
 in (LrTable.NT 6,(result,YENUM1left,RCURLY1right),rest671) end
| (130,(_,(_,_,RCURLYright as RCURLY1right))::_::(_,(
MlyValue.enumerator_list enumerator_list1,_,_))::_::(_,(_,YENUMleft
 as YENUM1left,YENUMright))::rest671) => let val result=
MlyValue.enum_specifier(fn _ => let val enumerator_list as 
enumerator_list1=enumerator_list1 ()
 in (
wrap((wrap(NONE, YENUMleft, YENUMright), enumerator_list),
                      YENUMleft, RCURLYright)
) end
)
 in (LrTable.NT 6,(result,YENUM1left,RCURLY1right),rest671) end
| (131,(_,(_,_,RCURLYright as RCURLY1right))::_::(_,(
MlyValue.enumerator_list enumerator_list1,_,_))::_::(_,(
MlyValue.struct_id struct_id1,_,_))::(_,(_,YENUMleft as YENUM1left,_))
::rest671) => let val result=MlyValue.enum_specifier(fn _ => let val 
struct_id as struct_id1=struct_id1 ()
val enumerator_list as enumerator_list1=enumerator_list1 ()
 in (
wrap((apnode SOME struct_id, enumerator_list),
                      YENUMleft, RCURLYright)
) end
)
 in (LrTable.NT 6,(result,YENUM1left,RCURLY1right),rest671) end
| (132,(_,(MlyValue.struct_id struct_id1,_,struct_idright as 
struct_id1right))::(_,(_,YENUMleft as YENUM1left,_))::rest671) => let 
val result=MlyValue.enum_specifier(fn _ => let val struct_id as 
struct_id1=struct_id1 ()
 in (wrap((apnode SOME struct_id, []), YENUMleft, struct_idright)) end
)
 in (LrTable.NT 6,(result,YENUM1left,struct_id1right),rest671) end
| (133,(_,(MlyValue.enumerator enumerator1,enumerator1left,
enumerator1right))::rest671) => let val result=
MlyValue.enumerator_list(fn _ => let val enumerator as enumerator1=
enumerator1 ()
 in ([enumerator]) end
)
 in (LrTable.NT 7,(result,enumerator1left,enumerator1right),rest671)
 end
| (134,(_,(MlyValue.enumerator enumerator1,_,enumerator1right))::_::(_
,(MlyValue.enumerator_list enumerator_list1,enumerator_list1left,_))::
rest671) => let val result=MlyValue.enumerator_list(fn _ => let val 
enumerator_list as enumerator_list1=enumerator_list1 ()
val enumerator as enumerator1=enumerator1 ()
 in (enumerator_list @ [enumerator]) end
)
 in (LrTable.NT 7,(result,enumerator_list1left,enumerator1right),
rest671) end
| (135,(_,(MlyValue.ID ID1,IDleft as ID1left,IDright as ID1right))::
rest671) => let val result=MlyValue.enumerator(fn _ => let val ID as 
ID1=ID1 ()
 in ((wrap(ID,IDleft,IDright), NONE)) end
)
 in (LrTable.NT 8,(result,ID1left,ID1right),rest671) end
| (136,(_,(MlyValue.rexpression rexpression1,_,rexpression1right))::_
::(_,(MlyValue.ID ID1,IDleft as ID1left,IDright))::rest671) => let 
val result=MlyValue.enumerator(fn _ => let val ID as ID1=ID1 ()
val rexpression as rexpression1=rexpression1 ()
 in ((wrap(ID,IDleft,IDright), SOME rexpression)) end
)
 in (LrTable.NT 8,(result,ID1left,rexpression1right),rest671) end
| (137,(_,(MlyValue.pointer pointer1,pointer1left,pointer1right))::
rest671) => let val result=MlyValue.abstract_declarator(fn _ => let 
val pointer as pointer1=pointer1 ()
 in (pointer) end
)
 in (LrTable.NT 60,(result,pointer1left,pointer1right),rest671) end
| (138,(_,(MlyValue.direct_abstract_declarator 
direct_abstract_declarator1,_,direct_abstract_declarator1right))::(_,(
MlyValue.pointer pointer1,pointer1left,_))::rest671) => let val result
=MlyValue.abstract_declarator(fn _ => let val pointer as pointer1=
pointer1 ()
val direct_abstract_declarator as direct_abstract_declarator1=
direct_abstract_declarator1 ()
 in (
wrap (node direct_abstract_declarator o
                                     node pointer,
                                     left pointer,
                                     right direct_abstract_declarator)
) end
)
 in (LrTable.NT 60,(result,pointer1left,
direct_abstract_declarator1right),rest671) end
| (139,(_,(MlyValue.direct_abstract_declarator 
direct_abstract_declarator1,direct_abstract_declarator1left,
direct_abstract_declarator1right))::rest671) => let val result=
MlyValue.abstract_declarator(fn _ => let val 
direct_abstract_declarator as direct_abstract_declarator1=
direct_abstract_declarator1 ()
 in (direct_abstract_declarator) end
)
 in (LrTable.NT 60,(result,direct_abstract_declarator1left,
direct_abstract_declarator1right),rest671) end
| (140,(_,(_,_,RPARENright as RPAREN1right))::(_,(
MlyValue.abstract_declarator abstract_declarator1,_,_))::(_,(_,
LPARENleft as LPAREN1left,_))::rest671) => let val result=
MlyValue.direct_abstract_declarator(fn _ => let val 
abstract_declarator as abstract_declarator1=abstract_declarator1 ()
 in (wrap(node abstract_declarator, LPARENleft, RPARENright)) end
)
 in (LrTable.NT 61,(result,LPAREN1left,RPAREN1right),rest671) end
| (141,(_,(_,_,RBRACKETright as RBRACKET1right))::(_,(
MlyValue.rexpression rexpression1,_,_))::(_,(_,LBRACKETleft as 
LBRACKET1left,_))::rest671) => let val result=
MlyValue.direct_abstract_declarator(fn _ => let val rexpression as 
rexpression1=rexpression1 ()
 in (arraydecl LBRACKETleft RBRACKETright (SOME rexpression)) end
)
 in (LrTable.NT 61,(result,LBRACKET1left,RBRACKET1right),rest671) end
| (142,(_,(_,_,RBRACKETright as RBRACKET1right))::(_,(_,LBRACKETleft
 as LBRACKET1left,_))::rest671) => let val result=
MlyValue.direct_abstract_declarator(fn _ => (
ptrdecl LBRACKETleft RBRACKETright))
 in (LrTable.NT 61,(result,LBRACKET1left,RBRACKET1right),rest671) end
| (143,(_,(_,_,RBRACKETright as RBRACKET1right))::(_,(
MlyValue.rexpression rexpression1,_,_))::(_,(_,LBRACKETleft,_))::(_,(
MlyValue.direct_abstract_declarator direct_abstract_declarator1,
direct_abstract_declarator1left,_))::rest671) => let val result=
MlyValue.direct_abstract_declarator(fn _ => let val 
direct_abstract_declarator as direct_abstract_declarator1=
direct_abstract_declarator1 ()
val rexpression as rexpression1=rexpression1 ()
 in (
ooa(direct_abstract_declarator,
                     arraydecl LBRACKETleft RBRACKETright (SOME rexpression))
) end
)
 in (LrTable.NT 61,(result,direct_abstract_declarator1left,
RBRACKET1right),rest671) end
| (144,(_,(_,_,RPARENright as RPAREN1right))::(_,(
MlyValue.parameter_list parameter_list1,_,_))::(_,(_,LPARENleft as 
LPAREN1left,_))::rest671) => let val result=
MlyValue.direct_abstract_declarator(fn _ => let val parameter_list as 
parameter_list1=parameter_list1 ()
 in (
let val ps = check_params ctxt parameter_list
                 in
                   fndecl LPARENleft RPARENright (map (#1 o node) ps)
                 end
) end
)
 in (LrTable.NT 61,(result,LPAREN1left,RPAREN1right),rest671) end
| (145,(_,(_,_,RPARENright as RPAREN1right))::(_,(
MlyValue.parameter_list parameter_list1,_,_))::(_,(_,LPARENleft,_))::(
_,(MlyValue.direct_abstract_declarator direct_abstract_declarator1,
direct_abstract_declarator1left,_))::rest671) => let val result=
MlyValue.direct_abstract_declarator(fn _ => let val 
direct_abstract_declarator as direct_abstract_declarator1=
direct_abstract_declarator1 ()
val parameter_list as parameter_list1=parameter_list1 ()
 in (
let val ps = check_params ctxt parameter_list
                 in
                   ooa(direct_abstract_declarator,
                       fndecl LPARENleft RPARENright (map (#1 o node) ps))
                 end
) end
)
 in (LrTable.NT 61,(result,direct_abstract_declarator1left,
RPAREN1right),rest671) end
| (146,(_,(MlyValue.abstract_declarator abstract_declarator1,_,
abstract_declarator1right))::(_,(MlyValue.specifier_qualifier_list 
specifier_qualifier_list1,specifier_qualifier_list1left,_))::rest671)
 => let val result=MlyValue.type_name(fn _ => let val 
specifier_qualifier_list as specifier_qualifier_list1=
specifier_qualifier_list1 ()
val abstract_declarator as abstract_declarator1=abstract_declarator1 
()
 in (
let
                   val sql = specifier_qualifier_list
                   val basety = extract_type ctxt sql
                   val _ = case has_typedef sql of
                             NONE => ()
                           | SOME (l,r) =>
                               errorStr' ctxt (l,r, "Typedef illegal here")
                 in
                   wrap(node abstract_declarator (node basety),
                        left specifier_qualifier_list,
                        right abstract_declarator)
                 end
) end
)
 in (LrTable.NT 33,(result,specifier_qualifier_list1left,
abstract_declarator1right),rest671) end
| (147,(_,(MlyValue.specifier_qualifier_list specifier_qualifier_list1
,specifier_qualifier_list1left,specifier_qualifier_list1right))::
rest671) => let val result=MlyValue.type_name(fn _ => let val 
specifier_qualifier_list as specifier_qualifier_list1=
specifier_qualifier_list1 ()
 in (
let
                   val sql = specifier_qualifier_list
                   val basety = extract_type ctxt sql
                   val _ = case has_typedef sql of
                             NONE => ()
                             | SOME (l,r) =>
                                 errorStr' ctxt (l,r, "Typedef illegal here")
                 in
                   basety
                 end
) end
)
 in (LrTable.NT 33,(result,specifier_qualifier_list1left,
specifier_qualifier_list1right),rest671) end
| (148,(_,(MlyValue.dinitializer dinitializer1,dinitializer1left,
dinitializer1right))::rest671) => let val result=
MlyValue.initializer_list(fn _ => let val dinitializer as 
dinitializer1=dinitializer1 ()
 in ([dinitializer]) end
)
 in (LrTable.NT 21,(result,dinitializer1left,dinitializer1right),
rest671) end
| (149,(_,(_,_,YCOMMA1right))::(_,(MlyValue.dinitializer dinitializer1
,dinitializer1left,_))::rest671) => let val result=
MlyValue.initializer_list(fn _ => let val dinitializer as 
dinitializer1=dinitializer1 ()
 in ([dinitializer]) end
)
 in (LrTable.NT 21,(result,dinitializer1left,YCOMMA1right),rest671)
 end
| (150,(_,(MlyValue.initializer_list initializer_list1,_,
initializer_list1right))::_::(_,(MlyValue.dinitializer dinitializer1,
dinitializer1left,_))::rest671) => let val result=
MlyValue.initializer_list(fn _ => let val dinitializer as 
dinitializer1=dinitializer1 ()
val initializer_list as initializer_list1=initializer_list1 ()
 in (dinitializer :: initializer_list) end
)
 in (LrTable.NT 21,(result,dinitializer1left,initializer_list1right),
rest671) end
| (151,(_,(MlyValue.initializer initializer1,_,initializer1right))::(_
,(MlyValue.designation designation1,designation1left,_))::rest671) => 
let val result=MlyValue.dinitializer(fn _ => let val designation as 
designation1=designation1 ()
val initializer as initializer1=initializer1 ()
 in ((designation, node initializer)) end
)
 in (LrTable.NT 22,(result,designation1left,initializer1right),rest671
) end
| (152,(_,(MlyValue.initializer initializer1,initializer1left,
initializer1right))::rest671) => let val result=MlyValue.dinitializer(
fn _ => let val initializer as initializer1=initializer1 ()
 in (([], node initializer)) end
)
 in (LrTable.NT 22,(result,initializer1left,initializer1right),rest671
) end
| (153,(_,(_,_,YEQ1right))::(_,(MlyValue.designator_list 
designator_list1,designator_list1left,_))::rest671) => let val result=
MlyValue.designation(fn _ => let val designator_list as 
designator_list1=designator_list1 ()
 in (designator_list) end
)
 in (LrTable.NT 24,(result,designator_list1left,YEQ1right),rest671)
 end
| (154,(_,(MlyValue.designator designator1,designator1left,
designator1right))::rest671) => let val result=
MlyValue.designator_list(fn _ => let val designator as designator1=
designator1 ()
 in ([designator]) end
)
 in (LrTable.NT 25,(result,designator1left,designator1right),rest671)
 end
| (155,(_,(MlyValue.designator_list designator_list1,_,
designator_list1right))::(_,(MlyValue.designator designator1,
designator1left,_))::rest671) => let val result=
MlyValue.designator_list(fn _ => let val designator as designator1=
designator1 ()
val designator_list as designator_list1=designator_list1 ()
 in (designator :: designator_list) end
)
 in (LrTable.NT 25,(result,designator1left,designator_list1right),
rest671) end
| (156,(_,(_,_,RBRACKET1right))::(_,(MlyValue.rexpression rexpression1
,_,_))::(_,(_,LBRACKET1left,_))::rest671) => let val result=
MlyValue.designator(fn _ => let val rexpression as rexpression1=
rexpression1 ()
 in (DesignE rexpression) end
)
 in (LrTable.NT 26,(result,LBRACKET1left,RBRACKET1right),rest671) end
| (157,(_,(MlyValue.ID ID1,_,ID1right))::(_,(_,YDOT1left,_))::rest671)
 => let val result=MlyValue.designator(fn _ => let val ID as ID1=ID1 
()
 in (DesignFld (C_field_name ID)) end
)
 in (LrTable.NT 26,(result,YDOT1left,ID1right),rest671) end
| (158,(_,(MlyValue.rexpression rexpression1,rexpression1left,
rexpression1right))::rest671) => let val result=MlyValue.initializer(
fn _ => let val rexpression as rexpression1=rexpression1 ()
 in (wrap(InitE rexpression, eleft rexpression, eright rexpression))
 end
)
 in (LrTable.NT 23,(result,rexpression1left,rexpression1right),rest671
) end
| (159,(_,(_,_,RCURLYright as RCURLY1right))::(_,(
MlyValue.initializer_list initializer_list1,_,_))::(_,(_,LCURLYleft
 as LCURLY1left,_))::rest671) => let val result=MlyValue.initializer(
fn _ => let val initializer_list as initializer_list1=
initializer_list1 ()
 in (wrap(InitList initializer_list, LCURLYleft, RCURLYright)) end
)
 in (LrTable.NT 23,(result,LCURLY1left,RCURLY1right),rest671) end
| (160,(_,(_,YEQ1left,YEQ1right))::rest671) => let val result=
MlyValue.assignop(fn _ => (NONE))
 in (LrTable.NT 57,(result,YEQ1left,YEQ1right),rest671) end
| (161,(_,(_,PLUSEQ1left,PLUSEQ1right))::rest671) => let val result=
MlyValue.assignop(fn _ => (SOME Plus))
 in (LrTable.NT 57,(result,PLUSEQ1left,PLUSEQ1right),rest671) end
| (162,(_,(_,MINUSEQ1left,MINUSEQ1right))::rest671) => let val result=
MlyValue.assignop(fn _ => (SOME Minus))
 in (LrTable.NT 57,(result,MINUSEQ1left,MINUSEQ1right),rest671) end
| (163,(_,(_,BOREQ1left,BOREQ1right))::rest671) => let val result=
MlyValue.assignop(fn _ => (SOME BitwiseOr))
 in (LrTable.NT 57,(result,BOREQ1left,BOREQ1right),rest671) end
| (164,(_,(_,BANDEQ1left,BANDEQ1right))::rest671) => let val result=
MlyValue.assignop(fn _ => (SOME BitwiseAnd))
 in (LrTable.NT 57,(result,BANDEQ1left,BANDEQ1right),rest671) end
| (165,(_,(_,BXOREQ1left,BXOREQ1right))::rest671) => let val result=
MlyValue.assignop(fn _ => (SOME BitwiseXOr))
 in (LrTable.NT 57,(result,BXOREQ1left,BXOREQ1right),rest671) end
| (166,(_,(_,MULEQ1left,MULEQ1right))::rest671) => let val result=
MlyValue.assignop(fn _ => (SOME Times))
 in (LrTable.NT 57,(result,MULEQ1left,MULEQ1right),rest671) end
| (167,(_,(_,DIVEQ1left,DIVEQ1right))::rest671) => let val result=
MlyValue.assignop(fn _ => (SOME Divides))
 in (LrTable.NT 57,(result,DIVEQ1left,DIVEQ1right),rest671) end
| (168,(_,(_,MODEQ1left,MODEQ1right))::rest671) => let val result=
MlyValue.assignop(fn _ => (SOME Modulus))
 in (LrTable.NT 57,(result,MODEQ1left,MODEQ1right),rest671) end
| (169,(_,(_,LSHIFTEQ1left,LSHIFTEQ1right))::rest671) => let val 
result=MlyValue.assignop(fn _ => (SOME LShift))
 in (LrTable.NT 57,(result,LSHIFTEQ1left,LSHIFTEQ1right),rest671) end
| (170,(_,(_,RSHIFTEQ1left,RSHIFTEQ1right))::rest671) => let val 
result=MlyValue.assignop(fn _ => (SOME RShift))
 in (LrTable.NT 57,(result,RSHIFTEQ1left,RSHIFTEQ1right),rest671) end
| (171,(_,(MlyValue.ID ID1,IDleft as ID1left,IDright as ID1right))::
rest671) => let val result=MlyValue.statement_label(fn _ => let val ID
 as ID1=ID1 ()
 in (wrap(ID,IDleft,IDright)) end
)
 in (LrTable.NT 44,(result,ID1left,ID1right),rest671) end
| (172,(_,(_,_,YSEMIright as YSEMI1right))::(_,(MlyValue.rexpression 
rexpression1,_,_))::(_,(MlyValue.assignop assignop1,_,_))::(_,(
MlyValue.lexpression lexpression1,lexpression1left,_))::rest671) => 
let val result=MlyValue.statement(fn _ => let val lexpression as 
lexpression1=lexpression1 ()
val assignop as assignop1=assignop1 ()
val rexpression as rexpression1=rexpression1 ()
 in (
swrap(parse_stdassignop ctxt (lexpression, assignop, rexpression),
             eleft lexpression, YSEMIright)
) end
)
 in (LrTable.NT 41,(result,lexpression1left,YSEMI1right),rest671) end
| (173,(_,(_,_,YSEMIright as YSEMI1right))::(_,(MlyValue.rexpression 
rexpression1,rexpression1left,_))::rest671) => let val result=
MlyValue.statement(fn _ => let val rexpression as rexpression1=
rexpression1 ()
 in (
let val e = delvoidcasts (handle_builtin_fns ctxt rexpression)
           val l = eleft rexpression and r = YSEMIright
           val empty = swrap (EmptyStmt, l, r)
       in
         case enode e of
           EFnCall(fn_e, args) => swrap(AssignFnCall(NONE, fn_e, args),l,r)
         | _ => if is_number e then empty
                else if fncall_free e then
                  (warnStr' ctxt (l, r,
                            "Ignoring (oddly expressed) expression without \
                            \side effect");
                   empty)
                else
                  (errorStr' ctxt (l, r, "Illegal bare expression containing \
                                   \function calls");
                   empty)
       end
) end
)
 in (LrTable.NT 41,(result,rexpression1left,YSEMI1right),rest671) end
| (174,(_,(MlyValue.statement statement1,_,statement1right))::(_,(
MlyValue.invariant_option invariant_option1,_,_))::_::(_,(
MlyValue.rexpression rexpression1,_,_))::_::(_,(_,YWHILEleft as 
YWHILE1left,_))::rest671) => let val result=MlyValue.statement(fn _
 => let val rexpression as rexpression1=rexpression1 ()
val invariant_option as invariant_option1=invariant_option1 ()
val statement as statement1=statement1 ()
 in (
let val body = swrap(Trap(ContinueT, statement), sleft statement,
                            sright statement)
           val loop = swrap(While(rexpression, invariant_option, body),
                            YWHILEleft, sright statement)
       in
         swrap(Trap(BreakT, loop), YWHILEleft, sright statement)
       end
) end
)
 in (LrTable.NT 41,(result,YWHILE1left,statement1right),rest671) end
| (175,(_,(_,_,YSEMIright as YSEMI1right))::_::(_,(
MlyValue.rexpression rexpression1,_,_))::_::_::(_,(MlyValue.statement 
statement1,_,_))::(_,(MlyValue.invariant_option invariant_option1,_,_)
)::(_,(_,YDOleft as YDO1left,_))::rest671) => let val result=
MlyValue.statement(fn _ => let val invariant_option as 
invariant_option1=invariant_option1 ()
val statement as statement1=statement1 ()
val rexpression as rexpression1=rexpression1 ()
 in (
let val body = swrap (Trap(ContinueT, statement),
                             sleft statement, sright statement)
           val loop = swrap(While(rexpression, invariant_option, body),
                            YDOleft, YSEMIright)
       in
         swrap(Trap(BreakT,
                    swrap(Block [BI_Stmt body, BI_Stmt loop],
                          sleft statement, YSEMIright)),
               YDOleft, YSEMIright)
       end
) end
)
 in (LrTable.NT 41,(result,YDO1left,YSEMI1right),rest671) end
| (176,(_,(MlyValue.statement statement1,_,statement1right))::(_,(
MlyValue.invariant_option invariant_option1,_,_))::_::(_,(
MlyValue.opt_for3_expr opt_for3_expr1,_,_))::_::(_,(
MlyValue.opt_for2_expr opt_for2_expr1,_,_))::(_,(
MlyValue.opt_for1_bitem opt_for1_bitem1,_,_))::_::(_,(_,YFORleft as 
YFOR1left,_))::rest671) => let val result=MlyValue.statement(fn _ => 
let val opt_for1_bitem as opt_for1_bitem1=opt_for1_bitem1 ()
val opt_for2_expr as opt_for2_expr1=opt_for2_expr1 ()
val opt_for3_expr as opt_for3_expr1=opt_for3_expr1 ()
val invariant_option as invariant_option1=invariant_option1 ()
val statement as statement1=statement1 ()
 in (
let val body0 = swrap(Trap(ContinueT, statement),
                             sleft statement, sright statement)
           val body = swrap(Block [BI_Stmt body0, BI_Stmt opt_for3_expr],
                            sleft statement, sright statement)
           val loop = swrap(While(opt_for2_expr, invariant_option, body),
                            YFORleft, sright statement)
           val tp_loop = swrap(Trap(BreakT, loop), YFORleft, sright statement)
       in
         swrap(Block (opt_for1_bitem @ [BI_Stmt tp_loop]),
               YFORleft, sright statement)
       end
) end
)
 in (LrTable.NT 41,(result,YFOR1left,statement1right),rest671) end
| (177,(_,(_,_,YSEMIright as YSEMI1right))::(_,(MlyValue.rexpression 
rexpression1,_,_))::(_,(_,YRETURNleft as YRETURN1left,_))::rest671)
 => let val result=MlyValue.statement(fn _ => let val rexpression as 
rexpression1=rexpression1 ()
 in (
case enode (handle_builtin_fns ctxt rexpression) of
         EFnCall(fn_e, args) =>
           swrap(ReturnFnCall (fn_e, args), YRETURNleft, YSEMIright)
       | e => swrap(Return (SOME rexpression),YRETURNleft,YSEMIright)
) end
)
 in (LrTable.NT 41,(result,YRETURN1left,YSEMI1right),rest671) end
| (178,(_,(_,_,YSEMIright as YSEMI1right))::(_,(_,YRETURNleft as 
YRETURN1left,_))::rest671) => let val result=MlyValue.statement(fn _
 => (swrap(Return NONE, YRETURNleft, YSEMIright)))
 in (LrTable.NT 41,(result,YRETURN1left,YSEMI1right),rest671) end
| (179,(_,(_,_,YSEMIright as YSEMI1right))::(_,(_,YBREAKleft as 
YBREAK1left,_))::rest671) => let val result=MlyValue.statement(fn _
 => (swrap(Break, YBREAKleft, YSEMIright)))
 in (LrTable.NT 41,(result,YBREAK1left,YSEMI1right),rest671) end
| (180,(_,(_,_,YSEMIright as YSEMI1right))::(_,(_,YCONTINUEleft as 
YCONTINUE1left,_))::rest671) => let val result=MlyValue.statement(fn _
 => (swrap(Continue,YCONTINUEleft,YSEMIright)))
 in (LrTable.NT 41,(result,YCONTINUE1left,YSEMI1right),rest671) end
| (181,(_,(_,_,YSEMIright as YSEMI1right))::(_,(
MlyValue.statement_label statement_label1,_,_))::(_,(_,YGOTOleft as 
YGOTO1left,_))::rest671) => let val result=MlyValue.statement(fn _ => 
let val statement_label as statement_label1=statement_label1 ()
 in (swrap(Goto (node statement_label), YGOTOleft, YSEMIright)) end
)
 in (LrTable.NT 41,(result,YGOTO1left,YSEMI1right),rest671) end
| (182,(_,(MlyValue.statement statement1,_,statement1right))::_::(_,(
MlyValue.rexpression rexpression1,_,_))::_::(_,(_,YIFleft as YIF1left,
_))::rest671) => let val result=MlyValue.statement(fn _ => let val 
rexpression as rexpression1=rexpression1 ()
val statement as statement1=statement1 ()
 in (
swrap(IfStmt (rexpression, statement,
                     swrap(EmptyStmt, defaultPos, defaultPos)),
             YIFleft,
             sright statement)
) end
)
 in (LrTable.NT 41,(result,YIF1left,statement1right),rest671) end
| (183,(_,(MlyValue.statement statement2,_,statement2right))::_::(_,(
MlyValue.statement statement1,_,_))::_::(_,(MlyValue.rexpression 
rexpression1,_,_))::_::(_,(_,YIFleft as YIF1left,_))::rest671) => let 
val result=MlyValue.statement(fn _ => let val rexpression as 
rexpression1=rexpression1 ()
val statement1=statement1 ()
val statement2=statement2 ()
 in (
swrap(IfStmt(rexpression, statement1, statement2), YIFleft,
             sright statement2)
) end
)
 in (LrTable.NT 41,(result,YIF1left,statement2right),rest671) end
| (184,(_,(_,YSEMIleft as YSEMI1left,YSEMIright as YSEMI1right))::
rest671) => let val result=MlyValue.statement(fn _ => (
swrap(EmptyStmt,YSEMIleft,YSEMIright)))
 in (LrTable.NT 41,(result,YSEMI1left,YSEMI1right),rest671) end
| (185,(_,(_,_,YSEMIright as YSEMI1right))::_::(_,(
MlyValue.lexpression lexpression1,lexpression1left,_))::rest671) => 
let val result=MlyValue.statement(fn _ => let val lexpression as 
lexpression1=lexpression1 ()
 in (swrap(postinc lexpression, eleft lexpression, YSEMIright)) end
)
 in (LrTable.NT 41,(result,lexpression1left,YSEMI1right),rest671) end
| (186,(_,(_,_,YSEMIright as YSEMI1right))::_::(_,(
MlyValue.lexpression lexpression1,lexpression1left,_))::rest671) => 
let val result=MlyValue.statement(fn _ => let val lexpression as 
lexpression1=lexpression1 ()
 in (swrap(postdec lexpression, eleft lexpression, YSEMIright)) end
)
 in (LrTable.NT 41,(result,lexpression1left,YSEMI1right),rest671) end
| (187,(_,(_,_,RCURLYright as RCURLY1right))::(_,(
MlyValue.switchcase_list switchcase_list1,_,_))::_::_::(_,(
MlyValue.rexpression rexpression1,_,_))::_::(_,(_,SWITCHleft as 
SWITCH1left,_))::rest671) => let val result=MlyValue.statement(fn _
 => let val rexpression as rexpression1=rexpression1 ()
val switchcase_list as switchcase_list1=switchcase_list1 ()
 in (
swrap(Trap(BreakT,
                  swrap(Switch(rexpression,
                               switch_check ctxt switchcase_list
                                            SWITCHleft RCURLYright),
                        SWITCHleft, RCURLYright)),
             SWITCHleft, RCURLYright)
) end
)
 in (LrTable.NT 41,(result,SWITCH1left,RCURLY1right),rest671) end
| (188,(_,(MlyValue.compound_statement compound_statement1,
compound_statement1left,compound_statement1right))::rest671) => let 
val result=MlyValue.statement(fn _ => let val compound_statement as 
compound_statement1=compound_statement1 ()
 in (
swrap(Block (node compound_statement), left compound_statement,
             right compound_statement)
) end
)
 in (LrTable.NT 41,(result,compound_statement1left,
compound_statement1right),rest671) end
| (189,(_,(MlyValue.statement statement1,_,statement1right))::_::(_,(
MlyValue.statement_label statement_label1,statement_label1left,_))::
rest671) => let val result=MlyValue.statement(fn _ => let val 
statement_label as statement_label1=statement_label1 ()
val statement as statement1=statement1 ()
 in (
swrap(LabeledStmt (node statement_label, statement), left statement_label, sright statement)
) end
)
 in (LrTable.NT 41,(result,statement_label1left,statement1right),
rest671) end
| (190,(_,(_,_,SPEC_BLOCKEND1right))::(_,(MlyValue.STRING_LITERAL 
STRING_LITERAL1,_,STRING_LITERALright))::(_,(_,AUXUPDleft as 
AUXUPD1left,_))::rest671) => let val result=MlyValue.statement(fn _
 => let val STRING_LITERAL as STRING_LITERAL1=STRING_LITERAL1 ()
 in (swrap(Auxupd STRING_LITERAL, AUXUPDleft, STRING_LITERALright))
 end
)
 in (LrTable.NT 41,(result,AUXUPD1left,SPEC_BLOCKEND1right),rest671)
 end
| (191,(_,(_,_,SPEC_BLOCKEND1right))::(_,(MlyValue.STRING_LITERAL 
STRING_LITERAL1,_,STRING_LITERALright))::(_,(_,GHOSTUPDleft as 
GHOSTUPD1left,_))::rest671) => let val result=MlyValue.statement(fn _
 => let val STRING_LITERAL as STRING_LITERAL1=STRING_LITERAL1 ()
 in (swrap(Ghostupd STRING_LITERAL, GHOSTUPDleft, STRING_LITERALright)
) end
)
 in (LrTable.NT 41,(result,GHOSTUPD1left,SPEC_BLOCKEND1right),rest671)
 end
| (192,(_,(_,_,SPEC_BLOCKEND2right))::(_,(MlyValue.STRING_LITERAL 
STRING_LITERAL2,_,_))::(_,(_,_,SPEC_ENDright))::(_,(
MlyValue.statement_list statement_list1,_,_))::_::(_,(
MlyValue.STRING_LITERAL STRING_LITERAL1,_,_))::(_,(_,SPEC_BEGINleft
 as SPEC_BEGIN1left,_))::rest671) => let val result=MlyValue.statement
(fn _ => let val STRING_LITERAL1=STRING_LITERAL1 ()
val statement_list as statement_list1=statement_list1 ()
val STRING_LITERAL2=STRING_LITERAL2 ()
 in (
let
        open Substring
        val ss = full STRING_LITERAL1
        val (before_fullstop, inc_stop) = splitl (fn c => c <> #".") ss
        val after_stop = triml 1 inc_stop
      in
        swrap(Spec((string before_fullstop, string after_stop),
                   statement_list,STRING_LITERAL2),
            SPEC_BEGINleft,
            SPEC_ENDright)
      end
) end
)
 in (LrTable.NT 41,(result,SPEC_BEGIN1left,SPEC_BLOCKEND2right),
rest671) end
| (193,(_,(_,_,YSEMIright as YSEMI1right))::_::(_,(MlyValue.asmblock 
asmblock1,_,_))::_::(_,(MlyValue.optvolatile optvolatile1,_,_))::(_,(_
,YASMleft as YASM1left,_))::rest671) => let val result=
MlyValue.statement(fn _ => let val optvolatile as optvolatile1=
optvolatile1 ()
val asmblock as asmblock1=asmblock1 ()
 in (
swrap(AsmStmt({volatilep = optvolatile, asmblock = asmblock}),
             YASMleft, YSEMIright)
) end
)
 in (LrTable.NT 41,(result,YASM1left,YSEMI1right),rest671) end
| (194,rest671) => let val result=MlyValue.optvolatile(fn _ => (false)
)
 in (LrTable.NT 4,(result,defaultPos,defaultPos),rest671) end
| (195,(_,(_,VOLATILE1left,VOLATILE1right))::rest671) => let val 
result=MlyValue.optvolatile(fn _ => (true))
 in (LrTable.NT 4,(result,VOLATILE1left,VOLATILE1right),rest671) end
| (196,(_,(MlyValue.asmmod1 asmmod11,_,asmmod11right))::(_,(
MlyValue.cstring_literal cstring_literal1,cstring_literal1left,_))::
rest671) => let val result=MlyValue.asmblock(fn _ => let val 
cstring_literal as cstring_literal1=cstring_literal1 ()
val asmmod1 as asmmod11=asmmod11 ()
 in (
{head = node cstring_literal,
                            mod1 = #1 asmmod1,
                            mod2 = #2 asmmod1,
                            mod3 = #3 asmmod1}
) end
)
 in (LrTable.NT 96,(result,cstring_literal1left,asmmod11right),rest671
) end
| (197,rest671) => let val result=MlyValue.asmmod1(fn _ => ([], [], []
))
 in (LrTable.NT 97,(result,defaultPos,defaultPos),rest671) end
| (198,(_,(MlyValue.asmmod2 asmmod21,_,asmmod21right))::(_,(
MlyValue.namedstringexplist namedstringexplist1,_,_))::(_,(_,
YCOLON1left,_))::rest671) => let val result=MlyValue.asmmod1(fn _ => 
let val namedstringexplist as namedstringexplist1=namedstringexplist1 
()
val asmmod2 as asmmod21=asmmod21 ()
 in (namedstringexplist, #1 asmmod2, #2 asmmod2) end
)
 in (LrTable.NT 97,(result,YCOLON1left,asmmod21right),rest671) end
| (199,rest671) => let val result=MlyValue.asmmod2(fn _ => ([], []))
 in (LrTable.NT 98,(result,defaultPos,defaultPos),rest671) end
| (200,(_,(MlyValue.asmmod3 asmmod31,_,asmmod31right))::(_,(
MlyValue.namedstringexplist namedstringexplist1,_,_))::(_,(_,
YCOLON1left,_))::rest671) => let val result=MlyValue.asmmod2(fn _ => 
let val namedstringexplist as namedstringexplist1=namedstringexplist1 
()
val asmmod3 as asmmod31=asmmod31 ()
 in ((namedstringexplist, asmmod3)) end
)
 in (LrTable.NT 98,(result,YCOLON1left,asmmod31right),rest671) end
| (201,rest671) => let val result=MlyValue.asmmod3(fn _ => ([]))
 in (LrTable.NT 99,(result,defaultPos,defaultPos),rest671) end
| (202,(_,(MlyValue.stringlist1 stringlist11,_,stringlist11right))::(_
,(_,YCOLON1left,_))::rest671) => let val result=MlyValue.asmmod3(fn _
 => let val stringlist1 as stringlist11=stringlist11 ()
 in (stringlist1) end
)
 in (LrTable.NT 99,(result,YCOLON1left,stringlist11right),rest671) end
| (203,(_,(MlyValue.cstring_literal cstring_literal1,
cstring_literal1left,cstring_literal1right))::rest671) => let val 
result=MlyValue.stringlist1(fn _ => let val cstring_literal as 
cstring_literal1=cstring_literal1 ()
 in ([node cstring_literal]) end
)
 in (LrTable.NT 101,(result,cstring_literal1left,cstring_literal1right
),rest671) end
| (204,(_,(MlyValue.stringlist1 stringlist11,_,stringlist11right))::_
::(_,(MlyValue.cstring_literal cstring_literal1,cstring_literal1left,_
))::rest671) => let val result=MlyValue.stringlist1(fn _ => let val 
cstring_literal as cstring_literal1=cstring_literal1 ()
val stringlist1 as stringlist11=stringlist11 ()
 in (node cstring_literal :: stringlist1) end
)
 in (LrTable.NT 101,(result,cstring_literal1left,stringlist11right),
rest671) end
| (205,rest671) => let val result=MlyValue.namedstringexplist(fn _ => 
([]))
 in (LrTable.NT 103,(result,defaultPos,defaultPos),rest671) end
| (206,(_,(MlyValue.namedstringexplist1 namedstringexplist11,
namedstringexplist11left,namedstringexplist11right))::rest671) => let 
val result=MlyValue.namedstringexplist(fn _ => let val 
namedstringexplist1 as namedstringexplist11=namedstringexplist11 ()
 in (namedstringexplist1) end
)
 in (LrTable.NT 103,(result,namedstringexplist11left,
namedstringexplist11right),rest671) end
| (207,(_,(MlyValue.namedstringexp namedstringexp1,namedstringexp1left
,namedstringexp1right))::rest671) => let val result=
MlyValue.namedstringexplist1(fn _ => let val namedstringexp as 
namedstringexp1=namedstringexp1 ()
 in ([namedstringexp]) end
)
 in (LrTable.NT 104,(result,namedstringexp1left,namedstringexp1right),
rest671) end
| (208,(_,(MlyValue.namedstringexplist1 namedstringexplist11,_,
namedstringexplist11right))::_::(_,(MlyValue.namedstringexp 
namedstringexp1,namedstringexp1left,_))::rest671) => let val result=
MlyValue.namedstringexplist1(fn _ => let val namedstringexp as 
namedstringexp1=namedstringexp1 ()
val namedstringexplist1 as namedstringexplist11=namedstringexplist11 
()
 in (namedstringexp :: namedstringexplist1) end
)
 in (LrTable.NT 104,(result,namedstringexp1left,
namedstringexplist11right),rest671) end
| (209,(_,(_,_,RPAREN1right))::(_,(MlyValue.rexpression rexpression1,_
,_))::_::(_,(MlyValue.cstring_literal cstring_literal1,
cstring_literal1left,_))::rest671) => let val result=
MlyValue.namedstringexp(fn _ => let val cstring_literal as 
cstring_literal1=cstring_literal1 ()
val rexpression as rexpression1=rexpression1 ()
 in ((NONE, node cstring_literal, rexpression)) end
)
 in (LrTable.NT 102,(result,cstring_literal1left,RPAREN1right),rest671
) end
| (210,(_,(_,_,RPAREN1right))::(_,(MlyValue.rexpression rexpression1,_
,_))::_::(_,(MlyValue.cstring_literal cstring_literal1,_,_))::_::(_,(
MlyValue.ID ID1,_,_))::(_,(_,LBRACKET1left,_))::rest671) => let val 
result=MlyValue.namedstringexp(fn _ => let val ID as ID1=ID1 ()
val cstring_literal as cstring_literal1=cstring_literal1 ()
val rexpression as rexpression1=rexpression1 ()
 in ((SOME ID, node cstring_literal, rexpression)) end
)
 in (LrTable.NT 102,(result,LBRACKET1left,RPAREN1right),rest671) end
| (211,(_,(_,_,SPEC_BLOCKEND1right))::(_,(MlyValue.STRING_LITERAL 
STRING_LITERAL1,STRING_LITERALleft,STRING_LITERALright))::(_,(_,
INVARIANT1left,_))::rest671) => let val result=MlyValue.invariant(fn _
 => let val STRING_LITERAL as STRING_LITERAL1=STRING_LITERAL1 ()
 in (wrap(STRING_LITERAL, STRING_LITERALleft, STRING_LITERALright))
 end
)
 in (LrTable.NT 17,(result,INVARIANT1left,SPEC_BLOCKEND1right),rest671
) end
| (212,rest671) => let val result=MlyValue.invariant_option(fn _ => (
NONE))
 in (LrTable.NT 18,(result,defaultPos,defaultPos),rest671) end
| (213,(_,(MlyValue.invariant invariant1,invariant1left,
invariant1right))::rest671) => let val result=
MlyValue.invariant_option(fn _ => let val invariant as invariant1=
invariant1 ()
 in (SOME invariant) end
)
 in (LrTable.NT 18,(result,invariant1left,invariant1right),rest671)
 end
| (214,rest671) => let val result=MlyValue.switchcase_list(fn _ => ([]
))
 in (LrTable.NT 45,(result,defaultPos,defaultPos),rest671) end
| (215,(_,(MlyValue.switchcase_list switchcase_list1,_,
switchcase_list1right))::(_,(MlyValue.switchcase switchcase1,
switchcase1left,_))::rest671) => let val result=
MlyValue.switchcase_list(fn _ => let val switchcase as switchcase1=
switchcase1 ()
val switchcase_list as switchcase_list1=switchcase_list1 ()
 in (switchcase :: switchcase_list) end
)
 in (LrTable.NT 45,(result,switchcase1left,switchcase_list1right),
rest671) end
| (216,(_,(MlyValue.block_item_list block_item_list1,_,
block_item_list1right))::(_,(MlyValue.statement statement1,_,_))::(_,(
MlyValue.labellist labellist1,labellist1left,_))::rest671) => let val 
result=MlyValue.switchcase(fn _ => let val labellist as labellist1=
labellist1 ()
val statement as statement1=statement1 ()
val block_item_list as block_item_list1=block_item_list1 ()
 in ((labellist, BI_Stmt statement :: block_item_list)) end
)
 in (LrTable.NT 46,(result,labellist1left,block_item_list1right),
rest671) end
| (217,(_,(MlyValue.label label1,label1left,label1right))::rest671)
 => let val result=MlyValue.labellist(fn _ => let val label as label1=
label1 ()
 in (wrap([label], left label, right label)) end
)
 in (LrTable.NT 47,(result,label1left,label1right),rest671) end
| (218,(_,(MlyValue.labellist labellist1,_,labellist1right))::(_,(
MlyValue.label label1,label1left,_))::rest671) => let val result=
MlyValue.labellist(fn _ => let val label as label1=label1 ()
val labellist as labellist1=labellist1 ()
 in (wrap(label::node labellist, left label, right labellist)) end
)
 in (LrTable.NT 47,(result,label1left,labellist1right),rest671) end
| (219,(_,(_,_,YCOLONright as YCOLON1right))::(_,(MlyValue.rexpression
 rexpression1,_,_))::(_,(_,CASEleft as CASE1left,_))::rest671) => let 
val result=MlyValue.label(fn _ => let val rexpression as rexpression1=
rexpression1 ()
 in (wrap(SOME rexpression, CASEleft, YCOLONright)) end
)
 in (LrTable.NT 48,(result,CASE1left,YCOLON1right),rest671) end
| (220,(_,(_,_,YCOLONright as YCOLON1right))::(_,(_,DEFAULTleft as 
DEFAULT1left,_))::rest671) => let val result=MlyValue.label(fn _ => (
wrap(NONE, DEFAULTleft, YCOLONright)))
 in (LrTable.NT 48,(result,DEFAULT1left,YCOLON1right),rest671) end
| (221,(_,(_,_,YSEMI1right))::(_,(MlyValue.opt_for1_expr 
opt_for1_expr1,opt_for1_expr1left,_))::rest671) => let val result=
MlyValue.opt_for1_bitem(fn _ => let val opt_for1_expr as 
opt_for1_expr1=opt_for1_expr1 ()
 in ([BI_Stmt opt_for1_expr]) end
)
 in (LrTable.NT 49,(result,opt_for1_expr1left,YSEMI1right),rest671)
 end
| (222,(_,(MlyValue.declaration declaration1,declaration1left,
declaration1right))::rest671) => let val result=
MlyValue.opt_for1_bitem(fn _ => let val declaration as declaration1=
declaration1 ()
 in (map BI_Decl declaration) end
)
 in (LrTable.NT 49,(result,declaration1left,declaration1right),rest671
) end
| (223,rest671) => let val result=MlyValue.opt_for1_expr(fn _ => (
swrap(EmptyStmt, defaultPos, defaultPos)))
 in (LrTable.NT 50,(result,defaultPos,defaultPos),rest671) end
| (224,(_,(MlyValue.opt_for1_expr0 opt_for1_expr01,opt_for1_expr01left
,opt_for1_expr01right))::rest671) => let val result=
MlyValue.opt_for1_expr(fn _ => let val opt_for1_expr0 as 
opt_for1_expr01=opt_for1_expr01 ()
 in (
if length opt_for1_expr0 = 1 then
         hd opt_for1_expr0
       else swrap(Block(map BI_Stmt opt_for1_expr0),
                  sleft (hd opt_for1_expr0),
                  sright (List.last opt_for1_expr0))
) end
)
 in (LrTable.NT 50,(result,opt_for1_expr01left,opt_for1_expr01right),
rest671) end
| (225,(_,(MlyValue.opt_for1_exprbase opt_for1_exprbase1,
opt_for1_exprbase1left,opt_for1_exprbase1right))::rest671) => let val 
result=MlyValue.opt_for1_expr0(fn _ => let val opt_for1_exprbase as 
opt_for1_exprbase1=opt_for1_exprbase1 ()
 in ([opt_for1_exprbase]) end
)
 in (LrTable.NT 51,(result,opt_for1_exprbase1left,
opt_for1_exprbase1right),rest671) end
| (226,(_,(MlyValue.opt_for1_expr0 opt_for1_expr01,_,
opt_for1_expr01right))::_::(_,(MlyValue.opt_for1_exprbase 
opt_for1_exprbase1,opt_for1_exprbase1left,_))::rest671) => let val 
result=MlyValue.opt_for1_expr0(fn _ => let val opt_for1_exprbase as 
opt_for1_exprbase1=opt_for1_exprbase1 ()
val opt_for1_expr0 as opt_for1_expr01=opt_for1_expr01 ()
 in (opt_for1_exprbase::opt_for1_expr0) end
)
 in (LrTable.NT 51,(result,opt_for1_exprbase1left,opt_for1_expr01right
),rest671) end
| (227,(_,(MlyValue.rexpression rexpression1,_,rexpression1right))::_
::(_,(MlyValue.lexpression lexpression1,lexpression1left,_))::rest671)
 => let val result=MlyValue.opt_for1_exprbase(fn _ => let val 
lexpression as lexpression1=lexpression1 ()
val rexpression as rexpression1=rexpression1 ()
 in (
swrap(Assign(lexpression,rexpression),
             eleft lexpression, eright rexpression)
) end
)
 in (LrTable.NT 52,(result,lexpression1left,rexpression1right),rest671
) end
| (228,rest671) => let val result=MlyValue.opt_for2_expr(fn _ => (
expr_int 1))
 in (LrTable.NT 53,(result,defaultPos,defaultPos),rest671) end
| (229,(_,(MlyValue.rexpression rexpression1,rexpression1left,
rexpression1right))::rest671) => let val result=MlyValue.opt_for2_expr
(fn _ => let val rexpression as rexpression1=rexpression1 ()
 in (rexpression) end
)
 in (LrTable.NT 53,(result,rexpression1left,rexpression1right),rest671
) end
| (230,rest671) => let val result=MlyValue.opt_for3_expr(fn _ => (
swrap(EmptyStmt,defaultPos,defaultPos)))
 in (LrTable.NT 54,(result,defaultPos,defaultPos),rest671) end
| (231,(_,(MlyValue.opt_for3_expr0 opt_for3_expr01,opt_for3_expr01left
,opt_for3_expr01right))::rest671) => let val result=
MlyValue.opt_for3_expr(fn _ => let val opt_for3_expr0 as 
opt_for3_expr01=opt_for3_expr01 ()
 in (
if length opt_for3_expr0 = 1 then
         hd opt_for3_expr0
       else swrap(Block(map BI_Stmt opt_for3_expr0),
                  sleft (hd opt_for3_expr0),
                  sright (List.last opt_for3_expr0))
) end
)
 in (LrTable.NT 54,(result,opt_for3_expr01left,opt_for3_expr01right),
rest671) end
| (232,(_,(MlyValue.opt_for3_exprbase opt_for3_exprbase1,
opt_for3_exprbase1left,opt_for3_exprbase1right))::rest671) => let val 
result=MlyValue.opt_for3_expr0(fn _ => let val opt_for3_exprbase as 
opt_for3_exprbase1=opt_for3_exprbase1 ()
 in ([opt_for3_exprbase]) end
)
 in (LrTable.NT 55,(result,opt_for3_exprbase1left,
opt_for3_exprbase1right),rest671) end
| (233,(_,(_,_,SPEC_BLOCKEND1right))::(_,(MlyValue.STRING_LITERAL 
STRING_LITERAL1,_,STRING_LITERALright))::(_,(_,AUXUPDleft,_))::(_,(
MlyValue.opt_for3_exprbase opt_for3_exprbase1,opt_for3_exprbase1left,_
))::rest671) => let val result=MlyValue.opt_for3_expr0(fn _ => let 
val opt_for3_exprbase as opt_for3_exprbase1=opt_for3_exprbase1 ()
val STRING_LITERAL as STRING_LITERAL1=STRING_LITERAL1 ()
 in (
[opt_for3_exprbase, swrap(Auxupd STRING_LITERAL, AUXUPDleft,
                                           STRING_LITERALright)]
) end
)
 in (LrTable.NT 55,(result,opt_for3_exprbase1left,SPEC_BLOCKEND1right)
,rest671) end
| (234,(_,(MlyValue.opt_for3_expr0 opt_for3_expr01,_,
opt_for3_expr01right))::_::(_,(MlyValue.opt_for3_exprbase 
opt_for3_exprbase1,opt_for3_exprbase1left,_))::rest671) => let val 
result=MlyValue.opt_for3_expr0(fn _ => let val opt_for3_exprbase as 
opt_for3_exprbase1=opt_for3_exprbase1 ()
val opt_for3_expr0 as opt_for3_expr01=opt_for3_expr01 ()
 in (opt_for3_exprbase::opt_for3_expr0) end
)
 in (LrTable.NT 55,(result,opt_for3_exprbase1left,opt_for3_expr01right
),rest671) end
| (235,(_,(MlyValue.rexpression rexpression1,_,rexpression1right))::(_
,(MlyValue.assignop assignop1,_,_))::(_,(MlyValue.lexpression 
lexpression1,lexpression1left,_))::rest671) => let val result=
MlyValue.opt_for3_exprbase(fn _ => let val lexpression as lexpression1
=lexpression1 ()
val assignop as assignop1=assignop1 ()
val rexpression as rexpression1=rexpression1 ()
 in (
swrap(parse_stdassignop ctxt (lexpression, assignop, rexpression),
             eleft lexpression, eright rexpression)
) end
)
 in (LrTable.NT 56,(result,lexpression1left,rexpression1right),rest671
) end
| (236,(_,(_,_,PLUSPLUSright as PLUSPLUS1right))::(_,(
MlyValue.lexpression lexpression1,lexpression1left,_))::rest671) => 
let val result=MlyValue.opt_for3_exprbase(fn _ => let val lexpression
 as lexpression1=lexpression1 ()
 in (
swrap(postinc lexpression, eleft lexpression,
                       PLUSPLUSright)
) end
)
 in (LrTable.NT 56,(result,lexpression1left,PLUSPLUS1right),rest671)
 end
| (237,(_,(_,_,MINUSMINUSright as MINUSMINUS1right))::(_,(
MlyValue.lexpression lexpression1,lexpression1left,_))::rest671) => 
let val result=MlyValue.opt_for3_exprbase(fn _ => let val lexpression
 as lexpression1=lexpression1 ()
 in (
swrap(postdec lexpression, eleft lexpression,
                       MINUSMINUSright)
) end
)
 in (LrTable.NT 56,(result,lexpression1left,MINUSMINUS1right),rest671)
 end
| (238,rest671) => let val result=MlyValue.opt_rexpr_list(fn _ => (
wrap([], defaultPos, defaultPos)))
 in (LrTable.NT 74,(result,defaultPos,defaultPos),rest671) end
| (239,(_,(MlyValue.rexpr_list rexpr_list1,rexpr_list1left,
rexpr_list1right))::rest671) => let val result=MlyValue.opt_rexpr_list
(fn _ => let val rexpr_list as rexpr_list1=rexpr_list1 ()
 in (rexpr_list) end
)
 in (LrTable.NT 74,(result,rexpr_list1left,rexpr_list1right),rest671)
 end
| (240,(_,(MlyValue.rexpression rexpression1,rexpression1left,
rexpression1right))::rest671) => let val result=MlyValue.rexpr_list(
fn _ => let val rexpression as rexpression1=rexpression1 ()
 in (
wrap([rexpression], eleft rexpression,
                               eright rexpression)
) end
)
 in (LrTable.NT 73,(result,rexpression1left,rexpression1right),rest671
) end
| (241,(_,(MlyValue.rexpr_list rexpr_list1,_,rexpr_list1right))::_::(_
,(MlyValue.rexpression rexpression1,rexpression1left,_))::rest671) => 
let val result=MlyValue.rexpr_list(fn _ => let val rexpression as 
rexpression1=rexpression1 ()
val rexpr_list as rexpr_list1=rexpr_list1 ()
 in (
wrap (rexpression :: node rexpr_list,
                       eleft rexpression, right rexpr_list)
) end
)
 in (LrTable.NT 73,(result,rexpression1left,rexpr_list1right),rest671)
 end
| (242,(_,(MlyValue.logical_OR_expression logical_OR_expression1,
logical_OR_expression1left,logical_OR_expression1right))::rest671) => 
let val result=MlyValue.rexpression(fn _ => let val 
logical_OR_expression as logical_OR_expression1=logical_OR_expression1
 ()
 in (logical_OR_expression) end
)
 in (LrTable.NT 72,(result,logical_OR_expression1left,
logical_OR_expression1right),rest671) end
| (243,(_,(MlyValue.rexpression rexpression2,_,rexpression2right))::_
::(_,(MlyValue.rexpression rexpression1,_,_))::_::(_,(
MlyValue.logical_OR_expression logical_OR_expression1,
logical_OR_expression1left,_))::rest671) => let val result=
MlyValue.rexpression(fn _ => let val logical_OR_expression as 
logical_OR_expression1=logical_OR_expression1 ()
val rexpression1=rexpression1 ()
val rexpression2=rexpression2 ()
 in (
ewrap(CondExp(logical_OR_expression, rexpression1,
                               rexpression2),
                       eleft logical_OR_expression,
                       eright rexpression2)
) end
)
 in (LrTable.NT 72,(result,logical_OR_expression1left,
rexpression2right),rest671) end
| (244,(_,(MlyValue.logical_AND_expression logical_AND_expression1,
logical_AND_expression1left,logical_AND_expression1right))::rest671)
 => let val result=MlyValue.logical_OR_expression(fn _ => let val 
logical_AND_expression as logical_AND_expression1=
logical_AND_expression1 ()
 in (logical_AND_expression) end
)
 in (LrTable.NT 76,(result,logical_AND_expression1left,
logical_AND_expression1right),rest671) end
| (245,(_,(MlyValue.logical_AND_expression logical_AND_expression1,_,
logical_AND_expression1right))::_::(_,(MlyValue.logical_OR_expression 
logical_OR_expression1,logical_OR_expression1left,_))::rest671) => 
let val result=MlyValue.logical_OR_expression(fn _ => let val 
logical_OR_expression as logical_OR_expression1=logical_OR_expression1
 ()
val logical_AND_expression as logical_AND_expression1=
logical_AND_expression1 ()
 in (
ewrap(BinOp(LogOr, logical_OR_expression,
                             logical_AND_expression),
                       eleft logical_OR_expression,
                       eright logical_AND_expression)
) end
)
 in (LrTable.NT 76,(result,logical_OR_expression1left,
logical_AND_expression1right),rest671) end
| (246,(_,(MlyValue.inclusive_OR_expression inclusive_OR_expression1,
inclusive_OR_expression1left,inclusive_OR_expression1right))::rest671)
 => let val result=MlyValue.logical_AND_expression(fn _ => let val 
inclusive_OR_expression as inclusive_OR_expression1=
inclusive_OR_expression1 ()
 in (inclusive_OR_expression) end
)
 in (LrTable.NT 75,(result,inclusive_OR_expression1left,
inclusive_OR_expression1right),rest671) end
| (247,(_,(MlyValue.inclusive_OR_expression inclusive_OR_expression1,_
,inclusive_OR_expression1right))::_::(_,(
MlyValue.logical_AND_expression logical_AND_expression1,
logical_AND_expression1left,_))::rest671) => let val result=
MlyValue.logical_AND_expression(fn _ => let val logical_AND_expression
 as logical_AND_expression1=logical_AND_expression1 ()
val inclusive_OR_expression as inclusive_OR_expression1=
inclusive_OR_expression1 ()
 in (
ewrap(BinOp(LogAnd, logical_AND_expression, inclusive_OR_expression),
                       eleft logical_AND_expression,
                       eright inclusive_OR_expression)
) end
)
 in (LrTable.NT 75,(result,logical_AND_expression1left,
inclusive_OR_expression1right),rest671) end
| (248,(_,(MlyValue.exclusive_OR_expression exclusive_OR_expression1,
exclusive_OR_expression1left,exclusive_OR_expression1right))::rest671)
 => let val result=MlyValue.inclusive_OR_expression(fn _ => let val 
exclusive_OR_expression as exclusive_OR_expression1=
exclusive_OR_expression1 ()
 in (exclusive_OR_expression) end
)
 in (LrTable.NT 77,(result,exclusive_OR_expression1left,
exclusive_OR_expression1right),rest671) end
| (249,(_,(MlyValue.exclusive_OR_expression exclusive_OR_expression1,_
,exclusive_OR_expression1right))::_::(_,(
MlyValue.inclusive_OR_expression inclusive_OR_expression1,
inclusive_OR_expression1left,_))::rest671) => let val result=
MlyValue.inclusive_OR_expression(fn _ => let val 
inclusive_OR_expression as inclusive_OR_expression1=
inclusive_OR_expression1 ()
val exclusive_OR_expression as exclusive_OR_expression1=
exclusive_OR_expression1 ()
 in (
ewrap(BinOp(BitwiseOr, inclusive_OR_expression,
                              exclusive_OR_expression),
                        eleft inclusive_OR_expression,
                        eright exclusive_OR_expression)
) end
)
 in (LrTable.NT 77,(result,inclusive_OR_expression1left,
exclusive_OR_expression1right),rest671) end
| (250,(_,(MlyValue.AND_expression AND_expression1,AND_expression1left
,AND_expression1right))::rest671) => let val result=
MlyValue.exclusive_OR_expression(fn _ => let val AND_expression as 
AND_expression1=AND_expression1 ()
 in (AND_expression) end
)
 in (LrTable.NT 78,(result,AND_expression1left,AND_expression1right),
rest671) end
| (251,(_,(MlyValue.AND_expression AND_expression1,_,
AND_expression1right))::_::(_,(MlyValue.exclusive_OR_expression 
exclusive_OR_expression1,exclusive_OR_expression1left,_))::rest671)
 => let val result=MlyValue.exclusive_OR_expression(fn _ => let val 
exclusive_OR_expression as exclusive_OR_expression1=
exclusive_OR_expression1 ()
val AND_expression as AND_expression1=AND_expression1 ()
 in (
ewrap(BinOp(BitwiseXOr, exclusive_OR_expression,
                              AND_expression),
                        eleft exclusive_OR_expression,
                        eright AND_expression)
) end
)
 in (LrTable.NT 78,(result,exclusive_OR_expression1left,
AND_expression1right),rest671) end
| (252,(_,(MlyValue.equality_expression equality_expression1,
equality_expression1left,equality_expression1right))::rest671) => let 
val result=MlyValue.AND_expression(fn _ => let val equality_expression
 as equality_expression1=equality_expression1 ()
 in (equality_expression) end
)
 in (LrTable.NT 79,(result,equality_expression1left,
equality_expression1right),rest671) end
| (253,(_,(MlyValue.equality_expression equality_expression1,_,
equality_expression1right))::_::(_,(MlyValue.AND_expression 
AND_expression1,AND_expression1left,_))::rest671) => let val result=
MlyValue.AND_expression(fn _ => let val AND_expression as 
AND_expression1=AND_expression1 ()
val equality_expression as equality_expression1=equality_expression1 
()
 in (
ewrap(BinOp(BitwiseAnd, AND_expression, equality_expression),
                       eleft AND_expression,
                       eright equality_expression)
) end
)
 in (LrTable.NT 79,(result,AND_expression1left,
equality_expression1right),rest671) end
| (254,(_,(MlyValue.relational_expression relational_expression1,
relational_expression1left,relational_expression1right))::rest671) => 
let val result=MlyValue.equality_expression(fn _ => let val 
relational_expression as relational_expression1=relational_expression1
 ()
 in (relational_expression) end
)
 in (LrTable.NT 80,(result,relational_expression1left,
relational_expression1right),rest671) end
| (255,(_,(MlyValue.relational_expression relational_expression1,_,
relational_expression1right))::_::(_,(MlyValue.equality_expression 
equality_expression1,equality_expression1left,_))::rest671) => let 
val result=MlyValue.equality_expression(fn _ => let val 
equality_expression as equality_expression1=equality_expression1 ()
val relational_expression as relational_expression1=
relational_expression1 ()
 in (
ewrap(BinOp(Equals, equality_expression, relational_expression),
                       eleft equality_expression,
                       eright relational_expression)
) end
)
 in (LrTable.NT 80,(result,equality_expression1left,
relational_expression1right),rest671) end
| (256,(_,(MlyValue.relational_expression relational_expression1,_,
relational_expression1right))::_::(_,(MlyValue.equality_expression 
equality_expression1,equality_expression1left,_))::rest671) => let 
val result=MlyValue.equality_expression(fn _ => let val 
equality_expression as equality_expression1=equality_expression1 ()
val relational_expression as relational_expression1=
relational_expression1 ()
 in (
ewrap(BinOp(NotEquals, equality_expression, relational_expression),
                       eleft equality_expression,
                       eright relational_expression)
) end
)
 in (LrTable.NT 80,(result,equality_expression1left,
relational_expression1right),rest671) end
| (257,(_,(MlyValue.shift_expression shift_expression1,
shift_expression1left,shift_expression1right))::rest671) => let val 
result=MlyValue.relational_expression(fn _ => let val shift_expression
 as shift_expression1=shift_expression1 ()
 in (shift_expression) end
)
 in (LrTable.NT 81,(result,shift_expression1left,
shift_expression1right),rest671) end
| (258,(_,(MlyValue.shift_expression shift_expression1,_,
shift_expression1right))::_::(_,(MlyValue.relational_expression 
relational_expression1,relational_expression1left,_))::rest671) => 
let val result=MlyValue.relational_expression(fn _ => let val 
relational_expression as relational_expression1=relational_expression1
 ()
val shift_expression as shift_expression1=shift_expression1 ()
 in (
ewrap(BinOp(Lt, relational_expression, shift_expression),
                       eleft relational_expression,
                       eright shift_expression)
) end
)
 in (LrTable.NT 81,(result,relational_expression1left,
shift_expression1right),rest671) end
| (259,(_,(MlyValue.shift_expression shift_expression1,_,
shift_expression1right))::_::(_,(MlyValue.relational_expression 
relational_expression1,relational_expression1left,_))::rest671) => 
let val result=MlyValue.relational_expression(fn _ => let val 
relational_expression as relational_expression1=relational_expression1
 ()
val shift_expression as shift_expression1=shift_expression1 ()
 in (
ewrap(BinOp(Gt, relational_expression, shift_expression),
                       eleft relational_expression,
                       eright shift_expression)
) end
)
 in (LrTable.NT 81,(result,relational_expression1left,
shift_expression1right),rest671) end
| (260,(_,(MlyValue.shift_expression shift_expression1,_,
shift_expression1right))::_::(_,(MlyValue.relational_expression 
relational_expression1,relational_expression1left,_))::rest671) => 
let val result=MlyValue.relational_expression(fn _ => let val 
relational_expression as relational_expression1=relational_expression1
 ()
val shift_expression as shift_expression1=shift_expression1 ()
 in (
ewrap(BinOp(Leq, relational_expression, shift_expression),
                       eleft relational_expression,
                       eright shift_expression)
) end
)
 in (LrTable.NT 81,(result,relational_expression1left,
shift_expression1right),rest671) end
| (261,(_,(MlyValue.shift_expression shift_expression1,_,
shift_expression1right))::_::(_,(MlyValue.relational_expression 
relational_expression1,relational_expression1left,_))::rest671) => 
let val result=MlyValue.relational_expression(fn _ => let val 
relational_expression as relational_expression1=relational_expression1
 ()
val shift_expression as shift_expression1=shift_expression1 ()
 in (
ewrap(BinOp(Geq, relational_expression, shift_expression),
                       eleft relational_expression,
                       eright shift_expression)
) end
)
 in (LrTable.NT 81,(result,relational_expression1left,
shift_expression1right),rest671) end
| (262,(_,(MlyValue.additive_expression additive_expression1,
additive_expression1left,additive_expression1right))::rest671) => let 
val result=MlyValue.shift_expression(fn _ => let val 
additive_expression as additive_expression1=additive_expression1 ()
 in (additive_expression) end
)
 in (LrTable.NT 83,(result,additive_expression1left,
additive_expression1right),rest671) end
| (263,(_,(MlyValue.additive_expression additive_expression1,_,
additive_expression1right))::_::(_,(MlyValue.shift_expression 
shift_expression1,shift_expression1left,_))::rest671) => let val 
result=MlyValue.shift_expression(fn _ => let val shift_expression as 
shift_expression1=shift_expression1 ()
val additive_expression as additive_expression1=additive_expression1 
()
 in (
ewrap(BinOp(LShift, shift_expression, additive_expression),
                        eleft shift_expression,
                        eright additive_expression)
) end
)
 in (LrTable.NT 83,(result,shift_expression1left,
additive_expression1right),rest671) end
| (264,(_,(MlyValue.additive_expression additive_expression1,_,
additive_expression1right))::_::(_,(MlyValue.shift_expression 
shift_expression1,shift_expression1left,_))::rest671) => let val 
result=MlyValue.shift_expression(fn _ => let val shift_expression as 
shift_expression1=shift_expression1 ()
val additive_expression as additive_expression1=additive_expression1 
()
 in (
ewrap(BinOp(RShift, shift_expression, additive_expression),
                        eleft shift_expression,
                        eright additive_expression)
) end
)
 in (LrTable.NT 83,(result,shift_expression1left,
additive_expression1right),rest671) end
| (265,(_,(MlyValue.multiplicative_expression 
multiplicative_expression1,multiplicative_expression1left,
multiplicative_expression1right))::rest671) => let val result=
MlyValue.additive_expression(fn _ => let val multiplicative_expression
 as multiplicative_expression1=multiplicative_expression1 ()
 in (multiplicative_expression) end
)
 in (LrTable.NT 82,(result,multiplicative_expression1left,
multiplicative_expression1right),rest671) end
| (266,(_,(MlyValue.multiplicative_expression 
multiplicative_expression1,_,multiplicative_expression1right))::_::(_,
(MlyValue.additive_expression additive_expression1,
additive_expression1left,_))::rest671) => let val result=
MlyValue.additive_expression(fn _ => let val additive_expression as 
additive_expression1=additive_expression1 ()
val multiplicative_expression as multiplicative_expression1=
multiplicative_expression1 ()
 in (
ewrap(BinOp(Plus, additive_expression, multiplicative_expression),
                     eleft additive_expression,
                     eright multiplicative_expression)
) end
)
 in (LrTable.NT 82,(result,additive_expression1left,
multiplicative_expression1right),rest671) end
| (267,(_,(MlyValue.multiplicative_expression 
multiplicative_expression1,_,multiplicative_expression1right))::_::(_,
(MlyValue.additive_expression additive_expression1,
additive_expression1left,_))::rest671) => let val result=
MlyValue.additive_expression(fn _ => let val additive_expression as 
additive_expression1=additive_expression1 ()
val multiplicative_expression as multiplicative_expression1=
multiplicative_expression1 ()
 in (
ewrap(BinOp(Minus, additive_expression, multiplicative_expression),
                     eleft additive_expression,
                     eright multiplicative_expression)
) end
)
 in (LrTable.NT 82,(result,additive_expression1left,
multiplicative_expression1right),rest671) end
| (268,(_,(MlyValue.cast_expression cast_expression1,
cast_expression1left,cast_expression1right))::rest671) => let val 
result=MlyValue.multiplicative_expression(fn _ => let val 
cast_expression as cast_expression1=cast_expression1 ()
 in (cast_expression) end
)
 in (LrTable.NT 84,(result,cast_expression1left,cast_expression1right)
,rest671) end
| (269,(_,(MlyValue.cast_expression cast_expression1,_,
cast_expression1right))::_::(_,(MlyValue.multiplicative_expression 
multiplicative_expression1,multiplicative_expression1left,_))::rest671
) => let val result=MlyValue.multiplicative_expression(fn _ => let 
val multiplicative_expression as multiplicative_expression1=
multiplicative_expression1 ()
val cast_expression as cast_expression1=cast_expression1 ()
 in (
ewrap(BinOp(Times, multiplicative_expression, cast_expression),
                eleft multiplicative_expression,
                eright cast_expression)
) end
)
 in (LrTable.NT 84,(result,multiplicative_expression1left,
cast_expression1right),rest671) end
| (270,(_,(MlyValue.cast_expression cast_expression1,_,
cast_expression1right))::_::(_,(MlyValue.multiplicative_expression 
multiplicative_expression1,multiplicative_expression1left,_))::rest671
) => let val result=MlyValue.multiplicative_expression(fn _ => let 
val multiplicative_expression as multiplicative_expression1=
multiplicative_expression1 ()
val cast_expression as cast_expression1=cast_expression1 ()
 in (
ewrap(BinOp(Divides, multiplicative_expression, cast_expression),
                eleft multiplicative_expression,
                eright cast_expression)
) end
)
 in (LrTable.NT 84,(result,multiplicative_expression1left,
cast_expression1right),rest671) end
| (271,(_,(MlyValue.cast_expression cast_expression1,_,
cast_expression1right))::_::(_,(MlyValue.multiplicative_expression 
multiplicative_expression1,multiplicative_expression1left,_))::rest671
) => let val result=MlyValue.multiplicative_expression(fn _ => let 
val multiplicative_expression as multiplicative_expression1=
multiplicative_expression1 ()
val cast_expression as cast_expression1=cast_expression1 ()
 in (
ewrap(BinOp(Modulus, multiplicative_expression, cast_expression),
                eleft multiplicative_expression,
                eright cast_expression)
) end
)
 in (LrTable.NT 84,(result,multiplicative_expression1left,
cast_expression1right),rest671) end
| (272,(_,(MlyValue.unary_expression unary_expression1,
unary_expression1left,unary_expression1right))::rest671) => let val 
result=MlyValue.cast_expression(fn _ => let val unary_expression as 
unary_expression1=unary_expression1 ()
 in (unary_expression) end
)
 in (LrTable.NT 86,(result,unary_expression1left,
unary_expression1right),rest671) end
| (273,(_,(MlyValue.cast_expression cast_expression1,_,
cast_expression1right))::_::(_,(MlyValue.type_name type_name1,_,_))::(
_,(_,LPARENleft as LPAREN1left,_))::rest671) => let val result=
MlyValue.cast_expression(fn _ => let val type_name as type_name1=
type_name1 ()
val cast_expression as cast_expression1=cast_expression1 ()
 in (
ewrap(TypeCast(type_name, cast_expression), LPARENleft,
              eright cast_expression)
) end
)
 in (LrTable.NT 86,(result,LPAREN1left,cast_expression1right),rest671)
 end
| (274,(_,(MlyValue.postfix_expression postfix_expression1,
postfix_expression1left,postfix_expression1right))::rest671) => let 
val result=MlyValue.unary_expression(fn _ => let val 
postfix_expression as postfix_expression1=postfix_expression1 ()
 in (postfix_expression) end
)
 in (LrTable.NT 85,(result,postfix_expression1left,
postfix_expression1right),rest671) end
| (275,(_,(MlyValue.cast_expression cast_expression1,_,
cast_expression1right))::(_,(_,YMINUSleft as YMINUS1left,_))::rest671)
 => let val result=MlyValue.unary_expression(fn _ => let val 
cast_expression as cast_expression1=cast_expression1 ()
 in (
ewrap(UnOp(Negate, cast_expression), YMINUSleft,
                       eright cast_expression)
) end
)
 in (LrTable.NT 85,(result,YMINUS1left,cast_expression1right),rest671)
 end
| (276,(_,(MlyValue.cast_expression cast_expression1,_,
cast_expression1right))::(_,(_,YNOTleft as YNOT1left,_))::rest671) => 
let val result=MlyValue.unary_expression(fn _ => let val 
cast_expression as cast_expression1=cast_expression1 ()
 in (
ewrap(UnOp(Not, cast_expression),
                       YNOTleft, eright cast_expression)
) end
)
 in (LrTable.NT 85,(result,YNOT1left,cast_expression1right),rest671)
 end
| (277,(_,(MlyValue.cast_expression cast_expression1,_,
cast_expression1right))::(_,(_,YBITNOTleft as YBITNOT1left,_))::
rest671) => let val result=MlyValue.unary_expression(fn _ => let val 
cast_expression as cast_expression1=cast_expression1 ()
 in (
ewrap(UnOp(BitNegate, cast_expression),
                       YBITNOTleft, eright cast_expression)
) end
)
 in (LrTable.NT 85,(result,YBITNOT1left,cast_expression1right),rest671
) end
| (278,(_,(MlyValue.cast_expression cast_expression1,_,
cast_expression1right))::(_,(_,YAMPERSANDleft as YAMPERSAND1left,_))::
rest671) => let val result=MlyValue.unary_expression(fn _ => let val 
cast_expression as cast_expression1=cast_expression1 ()
 in (
ewrap(UnOp(Addr, cast_expression),
                       YAMPERSANDleft, eright cast_expression)
) end
)
 in (LrTable.NT 85,(result,YAMPERSAND1left,cast_expression1right),
rest671) end
| (279,(_,(MlyValue.cast_expression cast_expression1,_,
cast_expression1right))::(_,(_,YSTARleft as YSTAR1left,_))::rest671)
 => let val result=MlyValue.unary_expression(fn _ => let val 
cast_expression as cast_expression1=cast_expression1 ()
 in (
ewrap(Deref cast_expression, YSTARleft,
                       eright cast_expression)
) end
)
 in (LrTable.NT 85,(result,YSTAR1left,cast_expression1right),rest671)
 end
| (280,(_,(MlyValue.unary_expression unary_expression1,_,
unary_expression1right))::(_,(_,YSIZEOFleft as YSIZEOF1left,_))::
rest671) => let val result=MlyValue.unary_expression(fn _ => let val 
unary_expression as unary_expression1=unary_expression1 ()
 in (
ewrap(Sizeof unary_expression, YSIZEOFleft,
                       eright unary_expression)
) end
)
 in (LrTable.NT 85,(result,YSIZEOF1left,unary_expression1right),
rest671) end
| (281,(_,(_,_,RPARENright as RPAREN1right))::(_,(MlyValue.type_name 
type_name1,_,_))::_::(_,(_,YSIZEOFleft as YSIZEOF1left,_))::rest671)
 => let val result=MlyValue.unary_expression(fn _ => let val type_name
 as type_name1=type_name1 ()
 in (ewrap(SizeofTy type_name, YSIZEOFleft, RPARENright)) end
)
 in (LrTable.NT 85,(result,YSIZEOF1left,RPAREN1right),rest671) end
| (282,(_,(_,_,RPARENright as RPAREN1right))::(_,(MlyValue.fieldlist 
fieldlist1,_,_))::_::(_,(MlyValue.type_specifier type_specifier1,_,_))
::_::(_,(_,YOFFSETOFleft as YOFFSETOF1left,_))::rest671) => let val 
result=MlyValue.unary_expression(fn _ => let val type_specifier as 
type_specifier1=type_specifier1 ()
val fieldlist as fieldlist1=fieldlist1 ()
 in (
let
                   val decls = wrap([TypeSpec type_specifier], tsleft type_specifier,
                               tsright type_specifier)
                   val ty = extract_type ctxt decls
                 in ewrap(OffsetOf (ty, fieldlist), YOFFSETOFleft, RPARENright) end
) end
)
 in (LrTable.NT 85,(result,YOFFSETOF1left,RPAREN1right),rest671) end
| (283,(_,(MlyValue.ID ID1,ID1left,ID1right))::rest671) => let val 
result=MlyValue.fieldlist(fn _ => let val ID as ID1=ID1 ()
 in ([C_field_name ID]) end
)
 in (LrTable.NT 91,(result,ID1left,ID1right),rest671) end
| (284,(_,(MlyValue.ID ID1,_,ID1right))::_::(_,(MlyValue.fieldlist 
fieldlist1,fieldlist1left,_))::rest671) => let val result=
MlyValue.fieldlist(fn _ => let val fieldlist as fieldlist1=fieldlist1 
()
val ID as ID1=ID1 ()
 in (fieldlist @ [C_field_name ID]) end
)
 in (LrTable.NT 91,(result,fieldlist1left,ID1right),rest671) end
| (285,(_,(MlyValue.primary_expression primary_expression1,
primary_expression1left,primary_expression1right))::rest671) => let 
val result=MlyValue.postfix_expression(fn _ => let val 
primary_expression as primary_expression1=primary_expression1 ()
 in (primary_expression) end
)
 in (LrTable.NT 87,(result,primary_expression1left,
primary_expression1right),rest671) end
| (286,(_,(_,_,RBRACKETright as RBRACKET1right))::(_,(
MlyValue.rexpression rexpression1,_,_))::_::(_,(
MlyValue.postfix_expression postfix_expression1,
postfix_expression1left,_))::rest671) => let val result=
MlyValue.postfix_expression(fn _ => let val postfix_expression as 
postfix_expression1=postfix_expression1 ()
val rexpression as rexpression1=rexpression1 ()
 in (
ewrap(ArrayDeref(postfix_expression, rexpression),
               eleft postfix_expression,
               RBRACKETright)
) end
)
 in (LrTable.NT 87,(result,postfix_expression1left,RBRACKET1right),
rest671) end
| (287,(_,(_,_,RPARENright as RPAREN1right))::(_,(
MlyValue.opt_rexpr_list opt_rexpr_list1,_,_))::_::(_,(
MlyValue.postfix_expression postfix_expression1,
postfix_expression1left,_))::rest671) => let val result=
MlyValue.postfix_expression(fn _ => let val postfix_expression as 
postfix_expression1=postfix_expression1 ()
val opt_rexpr_list as opt_rexpr_list1=opt_rexpr_list1 ()
 in (
let
           val e = ewrap(EFnCall(postfix_expression, node opt_rexpr_list),
                         eleft postfix_expression,
                         RPARENright)
         in
           handle_builtin_fns ctxt e
         end
) end
)
 in (LrTable.NT 87,(result,postfix_expression1left,RPAREN1right),
rest671) end
| (288,(_,(MlyValue.ID ID1,_,IDright as ID1right))::_::(_,(
MlyValue.postfix_expression postfix_expression1,
postfix_expression1left,_))::rest671) => let val result=
MlyValue.postfix_expression(fn _ => let val postfix_expression as 
postfix_expression1=postfix_expression1 ()
val ID as ID1=ID1 ()
 in (
ewrap(StructDot(postfix_expression, C_field_name ID),
               eleft postfix_expression,
               IDright)
) end
)
 in (LrTable.NT 87,(result,postfix_expression1left,ID1right),rest671)
 end
| (289,(_,(MlyValue.ID ID1,_,IDright as ID1right))::_::(_,(
MlyValue.postfix_expression postfix_expression1,
postfix_expression1left,_))::rest671) => let val result=
MlyValue.postfix_expression(fn _ => let val postfix_expression as 
postfix_expression1=postfix_expression1 ()
val ID as ID1=ID1 ()
 in (
ewrap(StructDot(ewrap(Deref postfix_expression,
                               eleft postfix_expression,
                               eright postfix_expression),
                         C_field_name ID),
               eleft postfix_expression,
               IDright)
) end
)
 in (LrTable.NT 87,(result,postfix_expression1left,ID1right),rest671)
 end
| (290,(_,(_,_,RCURLYright as RCURLY1right))::(_,(
MlyValue.initializer_list initializer_list1,_,_))::_::_::(_,(
MlyValue.type_name type_name1,_,_))::(_,(_,LPARENleft as LPAREN1left,_
))::rest671) => let val result=MlyValue.postfix_expression(fn _ => 
let val type_name as type_name1=type_name1 ()
val initializer_list as initializer_list1=initializer_list1 ()
 in (
ewrap(CompLiteral(node type_name, initializer_list),
                LPARENleft, RCURLYright)
) end
)
 in (LrTable.NT 87,(result,LPAREN1left,RCURLY1right),rest671) end
| (291,(_,(MlyValue.ID ID1,IDleft as ID1left,IDright as ID1right))::
rest671) => let val result=MlyValue.primary_expression(fn _ => let 
val ID as ID1=ID1 ()
 in (ewrap(Var (ID, Unsynchronized.ref NONE), IDleft, IDright)) end
)
 in (LrTable.NT 88,(result,ID1left,ID1right),rest671) end
| (292,(_,(MlyValue.constant constant1,constant1left,constant1right))
::rest671) => let val result=MlyValue.primary_expression(fn _ => let 
val constant as constant1=constant1 ()
 in (ewrap(Constant constant, left constant, right constant)) end
)
 in (LrTable.NT 88,(result,constant1left,constant1right),rest671) end
| (293,(_,(_,_,RPARENright as RPAREN1right))::(_,(MlyValue.rexpression
 rexpression1,_,_))::(_,(_,LPARENleft as LPAREN1left,_))::rest671) => 
let val result=MlyValue.primary_expression(fn _ => let val rexpression
 as rexpression1=rexpression1 ()
 in (ewrap(enode rexpression, LPARENleft, RPARENright)) end
)
 in (LrTable.NT 88,(result,LPAREN1left,RPAREN1right),rest671) end
| (294,(_,(MlyValue.cstring_literal cstring_literal1,
cstring_literal1left,cstring_literal1right))::rest671) => let val 
result=MlyValue.primary_expression(fn _ => let val cstring_literal as 
cstring_literal1=cstring_literal1 ()
 in (
let val l = left cstring_literal  and r = right cstring_literal
        in
          ewrap(Constant (wrap (STRING_LIT (node cstring_literal), l, r)), l, r)
        end
) end
)
 in (LrTable.NT 88,(result,cstring_literal1left,cstring_literal1right)
,rest671) end
| (295,(_,(MlyValue.STRING_LITERAL STRING_LITERAL1,_,
STRING_LITERALright as STRING_LITERAL1right))::(_,(
MlyValue.cstring_literal cstring_literal1,cstring_literal1left,_))::
rest671) => let val result=MlyValue.cstring_literal(fn _ => let val 
cstring_literal as cstring_literal1=cstring_literal1 ()
val STRING_LITERAL as STRING_LITERAL1=STRING_LITERAL1 ()
 in (
wrap(node cstring_literal ^ STRING_LITERAL, left cstring_literal,
             STRING_LITERALright)
) end
)
 in (LrTable.NT 100,(result,cstring_literal1left,STRING_LITERAL1right)
,rest671) end
| (296,(_,(MlyValue.STRING_LITERAL STRING_LITERAL1,STRING_LITERALleft
 as STRING_LITERAL1left,STRING_LITERALright as STRING_LITERAL1right))
::rest671) => let val result=MlyValue.cstring_literal(fn _ => let val 
STRING_LITERAL as STRING_LITERAL1=STRING_LITERAL1 ()
 in (wrap(STRING_LITERAL, STRING_LITERALleft, STRING_LITERALright))
 end
)
 in (LrTable.NT 100,(result,STRING_LITERAL1left,STRING_LITERAL1right),
rest671) end
| (297,(_,(MlyValue.NUMERIC_CONSTANT NUMERIC_CONSTANT1,
NUMERIC_CONSTANTleft as NUMERIC_CONSTANT1left,NUMERIC_CONSTANTright
 as NUMERIC_CONSTANT1right))::rest671) => let val result=
MlyValue.constant(fn _ => let val NUMERIC_CONSTANT as 
NUMERIC_CONSTANT1=NUMERIC_CONSTANT1 ()
 in (
wrap(NUMCONST NUMERIC_CONSTANT,
                                  NUMERIC_CONSTANTleft,
                                  NUMERIC_CONSTANTright)
) end
)
 in (LrTable.NT 89,(result,NUMERIC_CONSTANT1left,
NUMERIC_CONSTANT1right),rest671) end
| (298,(_,(MlyValue.postfix_expression postfix_expression1,
postfix_expression1left,postfix_expression1right))::rest671) => let 
val result=MlyValue.lexpression(fn _ => let val postfix_expression as 
postfix_expression1=postfix_expression1 ()
 in (postfix_expression) end
)
 in (LrTable.NT 71,(result,postfix_expression1left,
postfix_expression1right),rest671) end
| (299,(_,(MlyValue.cast_expression cast_expression1,_,
cast_expression1right))::(_,(_,YSTARleft as YSTAR1left,_))::rest671)
 => let val result=MlyValue.lexpression(fn _ => let val 
cast_expression as cast_expression1=cast_expression1 ()
 in (
ewrap(Deref cast_expression, YSTARleft,
                                      eright cast_expression)
) end
)
 in (LrTable.NT 71,(result,YSTAR1left,cast_expression1right),rest671)
 end
| _ => raise (mlyAction i392)
end
val void = MlyValue.VOID'
val extract = fn a => (fn MlyValue.begin x => x
| _ => let exception ParseInternal
	in raise ParseInternal end) a ()
end
end
structure Tokens : StrictC_TOKENS =
struct
type svalue = ParserData.svalue
type ('a,'b) token = ('a,'b) Token.token
fun EOF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 0,(
ParserData.MlyValue.VOID',p1,p2))
fun YSTAR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 1,(
ParserData.MlyValue.VOID',p1,p2))
fun SLASH (p1,p2) = Token.TOKEN (ParserData.LrTable.T 2,(
ParserData.MlyValue.VOID',p1,p2))
fun MOD (p1,p2) = Token.TOKEN (ParserData.LrTable.T 3,(
ParserData.MlyValue.VOID',p1,p2))
fun LPAREN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 4,(
ParserData.MlyValue.VOID',p1,p2))
fun RPAREN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 5,(
ParserData.MlyValue.VOID',p1,p2))
fun LCURLY (p1,p2) = Token.TOKEN (ParserData.LrTable.T 6,(
ParserData.MlyValue.VOID',p1,p2))
fun RCURLY (p1,p2) = Token.TOKEN (ParserData.LrTable.T 7,(
ParserData.MlyValue.VOID',p1,p2))
fun LBRACKET (p1,p2) = Token.TOKEN (ParserData.LrTable.T 8,(
ParserData.MlyValue.VOID',p1,p2))
fun RBRACKET (p1,p2) = Token.TOKEN (ParserData.LrTable.T 9,(
ParserData.MlyValue.VOID',p1,p2))
fun YCOMMA (p1,p2) = Token.TOKEN (ParserData.LrTable.T 10,(
ParserData.MlyValue.VOID',p1,p2))
fun YSEMI (p1,p2) = Token.TOKEN (ParserData.LrTable.T 11,(
ParserData.MlyValue.VOID',p1,p2))
fun YCOLON (p1,p2) = Token.TOKEN (ParserData.LrTable.T 12,(
ParserData.MlyValue.VOID',p1,p2))
fun QMARK (p1,p2) = Token.TOKEN (ParserData.LrTable.T 13,(
ParserData.MlyValue.VOID',p1,p2))
fun YEQ (p1,p2) = Token.TOKEN (ParserData.LrTable.T 14,(
ParserData.MlyValue.VOID',p1,p2))
fun YDOT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 15,(
ParserData.MlyValue.VOID',p1,p2))
fun YPLUS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 16,(
ParserData.MlyValue.VOID',p1,p2))
fun YMINUS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 17,(
ParserData.MlyValue.VOID',p1,p2))
fun YAND (p1,p2) = Token.TOKEN (ParserData.LrTable.T 18,(
ParserData.MlyValue.VOID',p1,p2))
fun YNOT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 19,(
ParserData.MlyValue.VOID',p1,p2))
fun YAMPERSAND (p1,p2) = Token.TOKEN (ParserData.LrTable.T 20,(
ParserData.MlyValue.VOID',p1,p2))
fun YBITNOT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 21,(
ParserData.MlyValue.VOID',p1,p2))
fun PLUSPLUS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 22,(
ParserData.MlyValue.VOID',p1,p2))
fun MINUSMINUS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 23,(
ParserData.MlyValue.VOID',p1,p2))
fun PLUSEQ (p1,p2) = Token.TOKEN (ParserData.LrTable.T 24,(
ParserData.MlyValue.VOID',p1,p2))
fun MINUSEQ (p1,p2) = Token.TOKEN (ParserData.LrTable.T 25,(
ParserData.MlyValue.VOID',p1,p2))
fun BANDEQ (p1,p2) = Token.TOKEN (ParserData.LrTable.T 26,(
ParserData.MlyValue.VOID',p1,p2))
fun BOREQ (p1,p2) = Token.TOKEN (ParserData.LrTable.T 27,(
ParserData.MlyValue.VOID',p1,p2))
fun MULEQ (p1,p2) = Token.TOKEN (ParserData.LrTable.T 28,(
ParserData.MlyValue.VOID',p1,p2))
fun DIVEQ (p1,p2) = Token.TOKEN (ParserData.LrTable.T 29,(
ParserData.MlyValue.VOID',p1,p2))
fun MODEQ (p1,p2) = Token.TOKEN (ParserData.LrTable.T 30,(
ParserData.MlyValue.VOID',p1,p2))
fun BXOREQ (p1,p2) = Token.TOKEN (ParserData.LrTable.T 31,(
ParserData.MlyValue.VOID',p1,p2))
fun LSHIFTEQ (p1,p2) = Token.TOKEN (ParserData.LrTable.T 32,(
ParserData.MlyValue.VOID',p1,p2))
fun RSHIFTEQ (p1,p2) = Token.TOKEN (ParserData.LrTable.T 33,(
ParserData.MlyValue.VOID',p1,p2))
fun YENUM (p1,p2) = Token.TOKEN (ParserData.LrTable.T 34,(
ParserData.MlyValue.VOID',p1,p2))
fun YIF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 35,(
ParserData.MlyValue.VOID',p1,p2))
fun YELSE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 36,(
ParserData.MlyValue.VOID',p1,p2))
fun YWHILE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 37,(
ParserData.MlyValue.VOID',p1,p2))
fun YDO (p1,p2) = Token.TOKEN (ParserData.LrTable.T 38,(
ParserData.MlyValue.VOID',p1,p2))
fun YRETURN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 39,(
ParserData.MlyValue.VOID',p1,p2))
fun YBREAK (p1,p2) = Token.TOKEN (ParserData.LrTable.T 40,(
ParserData.MlyValue.VOID',p1,p2))
fun YCONTINUE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 41,(
ParserData.MlyValue.VOID',p1,p2))
fun YGOTO (p1,p2) = Token.TOKEN (ParserData.LrTable.T 42,(
ParserData.MlyValue.VOID',p1,p2))
fun YFOR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 43,(
ParserData.MlyValue.VOID',p1,p2))
fun SWITCH (p1,p2) = Token.TOKEN (ParserData.LrTable.T 44,(
ParserData.MlyValue.VOID',p1,p2))
fun CASE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 45,(
ParserData.MlyValue.VOID',p1,p2))
fun DEFAULT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 46,(
ParserData.MlyValue.VOID',p1,p2))
fun YSIZEOF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 47,(
ParserData.MlyValue.VOID',p1,p2))
fun YTYPEOF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 48,(
ParserData.MlyValue.VOID',p1,p2))
fun YOFFSETOF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 49,(
ParserData.MlyValue.VOID',p1,p2))
fun LOGICALOR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 50,(
ParserData.MlyValue.VOID',p1,p2))
fun LOGICALAND (p1,p2) = Token.TOKEN (ParserData.LrTable.T 51,(
ParserData.MlyValue.VOID',p1,p2))
fun BITWISEOR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 52,(
ParserData.MlyValue.VOID',p1,p2))
fun BITWISEXOR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 53,(
ParserData.MlyValue.VOID',p1,p2))
fun EQUALS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 54,(
ParserData.MlyValue.VOID',p1,p2))
fun NOTEQUALS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 55,(
ParserData.MlyValue.VOID',p1,p2))
fun YLE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 56,(
ParserData.MlyValue.VOID',p1,p2))
fun YGE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 57,(
ParserData.MlyValue.VOID',p1,p2))
fun YLESS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 58,(
ParserData.MlyValue.VOID',p1,p2))
fun YGREATER (p1,p2) = Token.TOKEN (ParserData.LrTable.T 59,(
ParserData.MlyValue.VOID',p1,p2))
fun LEFTSHIFT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 60,(
ParserData.MlyValue.VOID',p1,p2))
fun RIGHTSHIFT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 61,(
ParserData.MlyValue.VOID',p1,p2))
fun INT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 62,(
ParserData.MlyValue.VOID',p1,p2))
fun BOOL (p1,p2) = Token.TOKEN (ParserData.LrTable.T 63,(
ParserData.MlyValue.VOID',p1,p2))
fun CHAR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 64,(
ParserData.MlyValue.VOID',p1,p2))
fun LONG (p1,p2) = Token.TOKEN (ParserData.LrTable.T 65,(
ParserData.MlyValue.VOID',p1,p2))
fun INT128 (p1,p2) = Token.TOKEN (ParserData.LrTable.T 66,(
ParserData.MlyValue.VOID',p1,p2))
fun SHORT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 67,(
ParserData.MlyValue.VOID',p1,p2))
fun SIGNED (p1,p2) = Token.TOKEN (ParserData.LrTable.T 68,(
ParserData.MlyValue.VOID',p1,p2))
fun UNSIGNED (p1,p2) = Token.TOKEN (ParserData.LrTable.T 69,(
ParserData.MlyValue.VOID',p1,p2))
fun VOID (p1,p2) = Token.TOKEN (ParserData.LrTable.T 70,(
ParserData.MlyValue.VOID',p1,p2))
fun ARROW (p1,p2) = Token.TOKEN (ParserData.LrTable.T 71,(
ParserData.MlyValue.VOID',p1,p2))
fun ID (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 72,(
ParserData.MlyValue.ID (fn () => i),p1,p2))
fun TYPEID (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 73,(
ParserData.MlyValue.TYPEID (fn () => i),p1,p2))
fun NUMERIC_CONSTANT (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 74
,(ParserData.MlyValue.NUMERIC_CONSTANT (fn () => i),p1,p2))
fun STRUCT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 75,(
ParserData.MlyValue.VOID',p1,p2))
fun UNION (p1,p2) = Token.TOKEN (ParserData.LrTable.T 76,(
ParserData.MlyValue.VOID',p1,p2))
fun TYPEDEF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 77,(
ParserData.MlyValue.VOID',p1,p2))
fun EXTERN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 78,(
ParserData.MlyValue.VOID',p1,p2))
fun CONST (p1,p2) = Token.TOKEN (ParserData.LrTable.T 79,(
ParserData.MlyValue.VOID',p1,p2))
fun VOLATILE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 80,(
ParserData.MlyValue.VOID',p1,p2))
fun RESTRICT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 81,(
ParserData.MlyValue.VOID',p1,p2))
fun INVARIANT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 82,(
ParserData.MlyValue.VOID',p1,p2))
fun INLINE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 83,(
ParserData.MlyValue.VOID',p1,p2))
fun STATIC (p1,p2) = Token.TOKEN (ParserData.LrTable.T 84,(
ParserData.MlyValue.VOID',p1,p2))
fun NORETURN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 85,(
ParserData.MlyValue.VOID',p1,p2))
fun THREAD_LOCAL (p1,p2) = Token.TOKEN (ParserData.LrTable.T 86,(
ParserData.MlyValue.VOID',p1,p2))
fun AUTO (p1,p2) = Token.TOKEN (ParserData.LrTable.T 87,(
ParserData.MlyValue.VOID',p1,p2))
fun FNSPEC (p1,p2) = Token.TOKEN (ParserData.LrTable.T 88,(
ParserData.MlyValue.VOID',p1,p2))
fun RELSPEC (p1,p2) = Token.TOKEN (ParserData.LrTable.T 89,(
ParserData.MlyValue.VOID',p1,p2))
fun AUXUPD (p1,p2) = Token.TOKEN (ParserData.LrTable.T 90,(
ParserData.MlyValue.VOID',p1,p2))
fun GHOSTUPD (p1,p2) = Token.TOKEN (ParserData.LrTable.T 91,(
ParserData.MlyValue.VOID',p1,p2))
fun MODIFIES (p1,p2) = Token.TOKEN (ParserData.LrTable.T 92,(
ParserData.MlyValue.VOID',p1,p2))
fun CALLS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 93,(
ParserData.MlyValue.VOID',p1,p2))
fun OWNED_BY (p1,p2) = Token.TOKEN (ParserData.LrTable.T 94,(
ParserData.MlyValue.VOID',p1,p2))
fun SPEC_BEGIN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 95,(
ParserData.MlyValue.VOID',p1,p2))
fun SPEC_END (p1,p2) = Token.TOKEN (ParserData.LrTable.T 96,(
ParserData.MlyValue.VOID',p1,p2))
fun DONT_TRANSLATE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 97,(
ParserData.MlyValue.VOID',p1,p2))
fun STRING_LITERAL (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 98,(
ParserData.MlyValue.STRING_LITERAL (fn () => i),p1,p2))
fun SPEC_BLOCKEND (p1,p2) = Token.TOKEN (ParserData.LrTable.T 99,(
ParserData.MlyValue.VOID',p1,p2))
fun GCC_ATTRIBUTE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 100,(
ParserData.MlyValue.VOID',p1,p2))
fun YASM (p1,p2) = Token.TOKEN (ParserData.LrTable.T 101,(
ParserData.MlyValue.VOID',p1,p2))
fun YREGISTER (p1,p2) = Token.TOKEN (ParserData.LrTable.T 102,(
ParserData.MlyValue.VOID',p1,p2))
end
end
