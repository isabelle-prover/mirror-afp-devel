(******************************************************************************
 * Isabelle/C
 *
 * Copyright (c) 2018-2019 Université Paris-Saclay, Univ. Paris-Sud, France
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *     * Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 *
 *     * Neither the name of the copyright holders nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 ******************************************************************************)

chapter \<open>Annex I: The Commented Sources of Isabelle/C\<close>

section \<open>Core Language: An Abstract Syntax Tree Definition (C Language without Annotations)\<close>

theory C_Ast
  imports Main
begin

subsection \<open>Loading the Generated AST\<close>

text \<open> The abstract syntax tree of the C language considered in the Isabelle/C project is
arbitrary, but it must already come with a grammar making the connection with a default AST, so that
both the grammar and AST can be imported to SML.\<^footnote>\<open>Additionally, the grammar and AST
must both have a free licence --- compatible with the Isabelle AFP, for them to be publishable
there.\<close> The Haskell Language.C project fulfills this property: see for instance
\<^url>\<open>http://hackage.haskell.org/package/language-c\<close> and
\<^url>\<open>https://github.com/visq/language-c/blob/master/src/Language/C/Syntax/AST.hs\<close>,
where its AST is being imported in the present theory file \<^file>\<open>C_Ast.thy\<close>, whereas
its grammar will be later in \<^file>\<open>C_Parser_Language.thy\<close>
(\<^file>\<open>C_Parser_Language.thy\<close> depends on \<^file>\<open>C_Ast.thy\<close>). The AST
importation is based on a modified version of Haskabelle, which generates the C AST from Haskell to
an ML file. \<close>

ML \<comment> \<open>\<^file>\<open>../generated/c_ast.ML\<close>\<close> \<open>
val fresh_ident0 =
  let val i = Synchronized.var "counter for new identifier" 38 in
    fn () => Int.toString (Synchronized.change_result i (fn i => (i, i + 1)))
  end
\<close>

ML \<comment> \<open>\<^file>\<open>../generated/c_ast.ML\<close>\<close> \<open>
\<comment> \<open>\<^url>\<open>https://gitlab.lisn.upsaclay.fr/burkhart.wolff/Isabelle_C/-/blob/C/Citadelle/src/compiler_generic/meta_isabelle/Printer_init.thy\<close>\<close>
structure CodeType = struct
  type mlInt = string
  type 'a mlMonad = 'a option
end

structure CodeConst = struct
  structure Monad = struct
    val bind = fn
        NONE => (fn _ => NONE)
      | SOME a => fn f => f a
    val return = SOME
  end

  structure Printf = struct
    local
      fun sprintf s l =
        case String.fields (fn #"%" => true | _ => false) s of
          [] => ""
        | [x] => x
        | x :: xs =>
            let fun aux acc l_pat l_s =
              case l_pat of
                [] => rev acc
              | x :: xs => aux (String.extract (x, 1, NONE) :: hd l_s :: acc) xs (tl l_s) in
            String.concat (x :: aux [] xs l)
      end
    in
      fun sprintf0 s_pat = s_pat
      fun sprintf1 s_pat s1 = sprintf s_pat [s1]
      fun sprintf2 s_pat s1 s2 = sprintf s_pat [s1, s2]
      fun sprintf3 s_pat s1 s2 s3 = sprintf s_pat [s1, s2, s3]
      fun sprintf4 s_pat s1 s2 s3 s4 = sprintf s_pat [s1, s2, s3, s4]
      fun sprintf5 s_pat s1 s2 s3 s4 s5 = sprintf s_pat [s1, s2, s3, s4, s5]
    end
  end

  structure String = struct
    val concat = String.concatWith
  end

  structure Sys = struct
    val isDirectory2 = SOME o File.is_dir o Path.explode handle ERROR _ => K NONE
  end

  structure To = struct
    fun nat f = Int.toString o f
  end

  fun outFile1 _ _ = tap (fn _ => warning "not implemented") NONE
  fun outStand1 f = outFile1 f ""
end
\<close>

ML_file \<open>../generated/c_ast.ML\<close>

text \<open> Note that the purpose of \<^dir>\<open>../generated\<close> is to host any generated
files of the Isabelle/C project. It contains among others:

  \<^item> \<^file>\<open>../generated/c_ast.ML\<close> representing the Abstract Syntax Tree of C,
  which has just been loaded.
  
  \<^item> \<^file>\<open>../generated/c_grammar_fun.grm\<close> is a generated file not used by the
  project, except for further generating \<^file>\<open>../generated/c_grammar_fun.grm.sig\<close>
  and \<^file>\<open>../generated/c_grammar_fun.grm.sml\<close>. Its physical presence in the
  directory is actually not necessary, but has been kept for informative documentation purposes. It
  represents the basis point of our SML grammar file, generated by an initial Haskell grammar file
  (namely
  \<^url>\<open>https://github.com/visq/language-c/blob/master/src/Language/C/Parser/Parser.y\<close>)
  using a modified version of Happy.

  \<^item> \<^file>\<open>../generated/c_grammar_fun.grm.sig\<close> and
  \<^file>\<open>../generated/c_grammar_fun.grm.sml\<close> are the two files generated from
  \<^file>\<open>../generated/c_grammar_fun.grm\<close> with a modified version of ML-Yacc. This
  last comes from MLton source in \<^dir>\<open>../../src_ext/mlton\<close>, see for example
  \<^dir>\<open>../../src_ext/mlton/mlyacc\<close>.
\<close>

text \<open> For the case of \<^file>\<open>../generated/c_ast.ML\<close>, it is actually not
mandatory to have a ``physical'' representation of the file in \<^dir>\<open>../generated\<close>:
it could be generated ``on-the-fly'' with \<^theory_text>\<open>code_reflect\<close> and immediately
loaded: Citadelle has an option to choose between the two
tasks~\<^cite>\<open>"DBLP:journals/afp/TuongW15"\<close>.\<^footnote>\<open>\<^url>\<open>https://gitlab.lisn.upsaclay.fr/frederictuong/isabelle_contrib/-/tree/master/Citadelle/src/compiler\<close>\<close>\<close>

text \<open> After loading the AST, it is possible in Citadelle to do various meta-programming
renaming, such as the one depicted in the next command. Actually, its content is explicitly included
here by hand since we decided to manually load the AST using the above
\<^theory_text>\<open>ML_file\<close> command. (Otherwise, one can automatically execute the overall
generation and renaming tasks in Citadelle without resorting to a manual copying-pasting.)\<close>

ML \<comment> \<open>\<^file>\<open>../generated/c_ast.ML\<close>\<close> \<open>
structure C_Ast =
struct
  val Position = C_Ast.position val NoPosition = C_Ast.noPosition val BuiltinPosition = C_Ast.builtinPosition val InternalPosition = C_Ast.internalPosition val Name = C_Ast.name val OnlyPos = C_Ast.onlyPos val NodeInfo = C_Ast.nodeInfo val AnonymousRef = C_Ast.anonymousRef val NamedRef = C_Ast.namedRef val CChar = C_Ast.cChar val CChars = C_Ast.cChars val DecRepr = C_Ast.decRepr val HexRepr = C_Ast.hexRepr val OctalRepr = C_Ast.octalRepr val FlagUnsigned = C_Ast.flagUnsigned val FlagLong = C_Ast.flagLong val FlagLongLong = C_Ast.flagLongLong val FlagImag = C_Ast.flagImag val CFloat = C_Ast.cFloat val Flags = C_Ast.flags val CInteger = C_Ast.cInteger val CAssignOp = C_Ast.cAssignOp val CMulAssOp = C_Ast.cMulAssOp val CDivAssOp = C_Ast.cDivAssOp val CRmdAssOp = C_Ast.cRmdAssOp val CAddAssOp = C_Ast.cAddAssOp val CSubAssOp = C_Ast.cSubAssOp val CShlAssOp = C_Ast.cShlAssOp val CShrAssOp = C_Ast.cShrAssOp val CAndAssOp = C_Ast.cAndAssOp val CXorAssOp = C_Ast.cXorAssOp val COrAssOp = C_Ast.cOrAssOp val CMulOp = C_Ast.cMulOp val CDivOp = C_Ast.cDivOp val CRmdOp = C_Ast.cRmdOp val CAddOp = C_Ast.cAddOp val CSubOp = C_Ast.cSubOp val CShlOp = C_Ast.cShlOp val CShrOp = C_Ast.cShrOp val CLeOp = C_Ast.cLeOp val CGrOp = C_Ast.cGrOp val CLeqOp = C_Ast.cLeqOp val CGeqOp = C_Ast.cGeqOp val CEqOp = C_Ast.cEqOp val CNeqOp = C_Ast.cNeqOp val CAndOp = C_Ast.cAndOp val CXorOp = C_Ast.cXorOp val COrOp = C_Ast.cOrOp val CLndOp = C_Ast.cLndOp val CLorOp = C_Ast.cLorOp val CPreIncOp = C_Ast.cPreIncOp val CPreDecOp = C_Ast.cPreDecOp val CPostIncOp = C_Ast.cPostIncOp val CPostDecOp = C_Ast.cPostDecOp val CAdrOp = C_Ast.cAdrOp val CIndOp = C_Ast.cIndOp val CPlusOp = C_Ast.cPlusOp val CMinOp = C_Ast.cMinOp val CCompOp = C_Ast.cCompOp val CNegOp = C_Ast.cNegOp val CAuto = C_Ast.cAuto val CRegister = C_Ast.cRegister val CStatic = C_Ast.cStatic val CExtern = C_Ast.cExtern val CTypedef = C_Ast.cTypedef val CThread = C_Ast.cThread val CInlineQual = C_Ast.cInlineQual val CNoreturnQual = C_Ast.cNoreturnQual val CStructTag = C_Ast.cStructTag val CUnionTag = C_Ast.cUnionTag val CIntConst = C_Ast.cIntConst val CCharConst = C_Ast.cCharConst val CFloatConst = C_Ast.cFloatConst val CStrConst = C_Ast.cStrConst val CStrLit = C_Ast.cStrLit val CFunDef = C_Ast.cFunDef val CDecl = C_Ast.cDecl val CStaticAssert = C_Ast.cStaticAssert val CDeclr = C_Ast.cDeclr val CPtrDeclr = C_Ast.cPtrDeclr val CArrDeclr = C_Ast.cArrDeclr val CFunDeclr = C_Ast.cFunDeclr val CNoArrSize = C_Ast.cNoArrSize val CArrSize = C_Ast.cArrSize val CLabel = C_Ast.cLabel val CCase = C_Ast.cCase val CCases = C_Ast.cCases val CDefault = C_Ast.cDefault val CExpr = C_Ast.cExpr val CCompound = C_Ast.cCompound val CIf = C_Ast.cIf val CSwitch = C_Ast.cSwitch val CWhile = C_Ast.cWhile val CFor = C_Ast.cFor val CGoto = C_Ast.cGoto val CGotoPtr = C_Ast.cGotoPtr val CCont = C_Ast.cCont val CBreak = C_Ast.cBreak val CReturn = C_Ast.cReturn val CAsm = C_Ast.cAsm val CAsmStmt = C_Ast.cAsmStmt val CAsmOperand = C_Ast.cAsmOperand val CBlockStmt = C_Ast.cBlockStmt val CBlockDecl = C_Ast.cBlockDecl val CNestedFunDef = C_Ast.cNestedFunDef val CStorageSpec = C_Ast.cStorageSpec val CTypeSpec = C_Ast.cTypeSpec val CTypeQual = C_Ast.cTypeQual val CFunSpec = C_Ast.cFunSpec val CAlignSpec = C_Ast.cAlignSpec val CVoidType = C_Ast.cVoidType val CCharType = C_Ast.cCharType val CShortType = C_Ast.cShortType val CIntType = C_Ast.cIntType val CLongType = C_Ast.cLongType val CFloatType = C_Ast.cFloatType val CDoubleType = C_Ast.cDoubleType val CSignedType = C_Ast.cSignedType val CUnsigType = C_Ast.cUnsigType val CBoolType = C_Ast.cBoolType val CComplexType = C_Ast.cComplexType val CInt128Type = C_Ast.cInt128Type val CSUType = C_Ast.cSUType val CEnumType = C_Ast.cEnumType val CTypeDef = C_Ast.cTypeDef val CTypeOfExpr = C_Ast.cTypeOfExpr val CTypeOfType = C_Ast.cTypeOfType val CAtomicType = C_Ast.cAtomicType val CConstQual = C_Ast.cConstQual val CVolatQual = C_Ast.cVolatQual val CRestrQual = C_Ast.cRestrQual val CAtomicQual = C_Ast.cAtomicQual val CAttrQual = C_Ast.cAttrQual val CNullableQual = C_Ast.cNullableQual val CNonnullQual = C_Ast.cNonnullQual val CAlignAsType = C_Ast.cAlignAsType val CAlignAsExpr = C_Ast.cAlignAsExpr val CStruct = C_Ast.cStruct val CEnum = C_Ast.cEnum val CInitExpr = C_Ast.cInitExpr val CInitList = C_Ast.cInitList val CArrDesig = C_Ast.cArrDesig val CMemberDesig = C_Ast.cMemberDesig val CRangeDesig = C_Ast.cRangeDesig val CAttr = C_Ast.cAttr val CComma = C_Ast.cComma val CAssign = C_Ast.cAssign val CCond = C_Ast.cCond val CBinary = C_Ast.cBinary val CCast = C_Ast.cCast val CUnary = C_Ast.cUnary val CSizeofExpr = C_Ast.cSizeofExpr val CSizeofType = C_Ast.cSizeofType val CAlignofExpr = C_Ast.cAlignofExpr val CAlignofType = C_Ast.cAlignofType val CComplexReal = C_Ast.cComplexReal val CComplexImag = C_Ast.cComplexImag val CIndex = C_Ast.cIndex val CCall = C_Ast.cCall val CMember = C_Ast.cMember val CVar = C_Ast.cVar val CConst = C_Ast.cConst val CCompoundLit = C_Ast.cCompoundLit val CGenericSelection = C_Ast.cGenericSelection val CStatExpr = C_Ast.cStatExpr val CLabAddrExpr = C_Ast.cLabAddrExpr val CBuiltinExpr = C_Ast.cBuiltinExpr val CBuiltinVaArg = C_Ast.cBuiltinVaArg val CBuiltinOffsetOf = C_Ast.cBuiltinOffsetOf val CBuiltinTypesCompatible = C_Ast.cBuiltinTypesCompatible val CDeclExt = C_Ast.cDeclExt val CFDefExt = C_Ast.cFDefExt val CAsmExt = C_Ast.cAsmExt val CTranslUnit = C_Ast.cTranslUnit
  open C_Ast
end
\<close>

subsection \<open>Basic Aliases and Initialization of the Haskell Library\<close>

ML \<comment> \<open>\<^file>\<open>../generated/c_ast.ML\<close>\<close> \<open>
structure C_Ast =
struct
type class_Pos = Position.T * Position.T
(**)
type NodeInfo = C_Ast.nodeInfo
type CStorageSpec = NodeInfo C_Ast.cStorageSpecifier
type CFunSpec = NodeInfo C_Ast.cFunctionSpecifier
type CConst = NodeInfo C_Ast.cConstant
type 'a CInitializerList = ('a C_Ast.cPartDesignator List.list * 'a C_Ast.cInitializer) List.list
type CTranslUnit = NodeInfo C_Ast.cTranslationUnit
type CExtDecl = NodeInfo C_Ast.cExternalDeclaration
type CFunDef = NodeInfo C_Ast.cFunctionDef
type CDecl = NodeInfo C_Ast.cDeclaration
type CDeclr = NodeInfo C_Ast.cDeclarator
type CDerivedDeclr = NodeInfo C_Ast.cDerivedDeclarator
type CArrSize = NodeInfo C_Ast.cArraySize
type CStat = NodeInfo C_Ast.cStatement
type CAsmStmt = NodeInfo C_Ast.cAssemblyStatement
type CAsmOperand = NodeInfo C_Ast.cAssemblyOperand
type CBlockItem = NodeInfo C_Ast.cCompoundBlockItem
type CDeclSpec = NodeInfo C_Ast.cDeclarationSpecifier
type CTypeSpec = NodeInfo C_Ast.cTypeSpecifier
type CTypeQual = NodeInfo C_Ast.cTypeQualifier
type CAlignSpec = NodeInfo C_Ast.cAlignmentSpecifier
type CStructUnion = NodeInfo C_Ast.cStructureUnion
type CEnum = NodeInfo C_Ast.cEnumeration
type CInit = NodeInfo C_Ast.cInitializer
type CInitList = NodeInfo CInitializerList
type CDesignator = NodeInfo C_Ast.cPartDesignator
type CAttr = NodeInfo C_Ast.cAttribute
type CExpr = NodeInfo C_Ast.cExpression
type CBuiltin = NodeInfo C_Ast.cBuiltinThing
type CStrLit = NodeInfo C_Ast.cStringLiteral
(**)
type ClangCVersion = C_Ast.clangCVersion
type Ident = C_Ast.ident
type Position = C_Ast.positiona
type PosLength = Position * int
type Name = C_Ast.namea
type Bool = bool
type CString = C_Ast.cString
type CChar = C_Ast.cChar
type CInteger = C_Ast.cInteger
type CFloat = C_Ast.cFloat
type CStructTag = C_Ast.cStructTag
type CUnaryOp = C_Ast.cUnaryOp
type 'a CStringLiteral = 'a C_Ast.cStringLiteral
type 'a CConstant = 'a C_Ast.cConstant
type ('a, 'b) Either = ('a, 'b) C_Ast.either
type CIntRepr = C_Ast.cIntRepr
type CIntFlag = C_Ast.cIntFlag
type CAssignOp = C_Ast.cAssignOp
type Comment = C_Ast.comment
(**)
type 'a Reversed = 'a
datatype CDeclrR = CDeclrR0 of C_Ast.ident C_Ast.optiona
                             * NodeInfo C_Ast.cDerivedDeclarator list Reversed
                             * NodeInfo C_Ast.cStringLiteral C_Ast.optiona
                             * NodeInfo C_Ast.cAttribute list
                             * NodeInfo
type 'a Maybe = 'a C_Ast.optiona
datatype 'a Located = Located of 'a * (Position * (Position * int))
(**)
fun CDeclrR ide l s a n = CDeclrR0 (ide, l, s, a, n)
val reverse = rev
val Nothing = C_Ast.None
val Just = C_Ast.Some
val False = false
val True = true
val Ident = C_Ast.Ident0
(**)
val CDecl_flat = fn l1 => C_Ast.CDecl l1 o map (fn (a, b, c) => ((a, b), c))
fun flat3 (a, b, c) = ((a, b), c)
fun maybe def f = fn C_Ast.None => def | C_Ast.Some x => f x 
val Reversed = I
(**)
val From_string =
    C_Ast.SS_base
  o C_Ast.ST
  o implode
  o map (fn s => \<comment> \<open>prevent functions in \<^file>\<open>~~/src/HOL/String.thy\<close> of raising additional errors
                     (e.g., see the ML code associated to \<^term>\<open>String.asciis_of_literal\<close>)\<close>
          if Symbol.is_char s then s
          else if Symbol.is_utf8 s then translate_string (fn c => "\\" ^ string_of_int (ord c)) s
          else s)
  o Symbol.explode
val From_char_hd = hd o C_Ast.explode
(**)
val Namea = C_Ast.name
(**)
open C_Ast
fun flip f b a = f a b
open Basic_Library
end
\<close>

section\<open>A General C11-AST iterator.\<close>

ML\<open>

signature C11_AST_LIB =
  sig
    (* some general combinators *)
    val fold_either: ('a -> 'b -> 'c) -> ('d -> 'b -> 'c) -> ('a, 'd) C_Ast.either -> 'b -> 'c
    val fold_optiona: ('a -> 'b -> 'b) -> 'a C_Ast.optiona -> 'b -> 'b

    datatype data = data_bool of bool     | data_int of int 
                  | data_string of string | data_absstring of string 

    type node_content = { tag     : string,
                          sub_tag : string,
                          args    : data list }

    (* conversions of enumeration types to string codes *)
    val toString_cBinaryOp : C_Ast.cBinaryOp -> string
    val toString_cIntFlag  : C_Ast.cIntFlag -> string
    val toString_cIntRepr  : C_Ast.cIntRepr -> string
    val toString_cUnaryOp  : C_Ast.cUnaryOp -> string
    val toString_cAssignOp : C_Ast.cAssignOp -> string
    val toString_abr_string: C_Ast.abr_string -> string
    val toString_nodeinfo  : C_Ast.nodeInfo -> string


    (* a generic iterator collection over the entire C11 - AST. The lexical 
       "leaves" of the AST's are parametric ('a). THe collecyot function "g" (see below)
       gets as additional parameter a string-key representing its term key
       (and sometimes local information such as enumeration type keys). *)
    (* Caveat : Assembly is currently not supported *)
    (* currently a special case since idents are not properly abstracted in the src files of the
       AST generation: *)
    val fold_ident: 'a -> (node_content -> 'a -> 'b -> 'c) -> C_Ast.ident -> 'b -> 'c
    (* the "Leaf" has to be delivered from the context, the internal non-parametric nodeinfo
       is currently ignored. HACK. *)

    val fold_cInteger: (node_content -> 'a -> 'b) -> C_Ast.cInteger -> 'a -> 'b
    val fold_cConstant: (node_content -> 'a -> 'b -> 'b) -> 'a C_Ast.cConstant -> 'b -> 'b
    val fold_cStringLiteral: (node_content -> 'a -> 'b -> 'b) -> 'a C_Ast.cStringLiteral -> 'b -> 'b


    val fold_cArraySize: 'a -> (node_content -> 'a -> 'b -> 'b) -> 'a C_Ast.cArraySize -> 'b -> 'b
    val fold_cAttribute: (node_content -> 'a -> 'b -> 'b) -> 'a C_Ast.cAttribute -> 'b -> 'b
    val fold_cBuiltinThing: (node_content -> 'a -> 'b -> 'b) -> 'a C_Ast.cBuiltinThing -> 'b -> 'b
    val fold_cCompoundBlockItem: (node_content -> 'a -> 'b -> 'b) 
                                    -> 'a C_Ast.cCompoundBlockItem -> 'b -> 'b
    val fold_cDeclaration: (node_content -> 'a -> 'b -> 'b) -> 'a C_Ast.cDeclaration -> 'b -> 'b
    val fold_cDeclarationSpecifier: (node_content -> 'a -> 'b -> 'b) 
                                    -> 'a C_Ast.cDeclarationSpecifier -> 'b -> 'b
    val fold_cDeclarator: (node_content -> 'a -> 'b -> 'b) -> 'a C_Ast.cDeclarator -> 'b -> 'b
    val fold_cDerivedDeclarator: (node_content -> 'a -> 'b -> 'b) 
                                    -> 'a C_Ast.cDerivedDeclarator -> 'b -> 'b
    val fold_cEnumeration: (node_content -> 'a -> 'b -> 'b) -> 'a C_Ast.cEnumeration -> 'b -> 'b
    val fold_cExpression: (node_content -> 'a -> 'b -> 'b) -> 'a C_Ast.cExpression -> 'b -> 'b
    val fold_cInitializer: (node_content -> 'a -> 'b -> 'b) -> 'a C_Ast.cInitializer -> 'b -> 'b
    val fold_cPartDesignator: (node_content -> 'a -> 'b -> 'b) -> 'a C_Ast.cPartDesignator -> 'b -> 'b
    val fold_cStatement: (node_content -> 'a -> 'b -> 'b) -> 'a C_Ast.cStatement -> 'b -> 'b
    val fold_cStructureUnion : (node_content -> 'a -> 'b -> 'b) -> 'a C_Ast.cStructureUnion -> 'b -> 'b 
    val fold_cTypeQualifier: (node_content -> 'a -> 'b -> 'b) -> 'a C_Ast.cTypeQualifier -> 'b -> 'b
    val fold_cTypeSpecifier: (node_content -> 'a -> 'b -> 'b) -> 'a C_Ast.cTypeSpecifier -> 'b -> 'b
    val fold_cExternalDeclaration: (node_content -> 'a -> 'b -> 'b) -> 'a C_Ast.cExternalDeclaration -> 'b -> 'b
    val fold_cTranslationUnit: (node_content -> 'a -> 'b -> 'b) -> 'a C_Ast.cTranslationUnit -> 'b -> 'b

  (* universal sum type : *)

    datatype 'a C11_Ast = 
           mk_cInteger              of    C_Ast.cInteger         
         | mk_cConstant             of 'a C_Ast.cConstant      
         | mk_cStringLiteral        of 'a C_Ast.cStringLiteral 
         | mk_cArraySize            of 'a C_Ast.cArraySize     
         | mk_cAttribute            of 'a C_Ast.cAttribute     
         | mk_cBuiltinThing         of 'a C_Ast.cBuiltinThing  
         | mk_cCompoundBlockItem    of 'a C_Ast.cCompoundBlockItem   
         | mk_cDeclaration          of 'a C_Ast.cDeclaration         
         | mk_cDeclarationSpecifier of 'a C_Ast.cDeclarationSpecifier
         | mk_cDeclarator           of 'a C_Ast.cDeclarator          
         | mk_cDerivedDeclarator    of 'a C_Ast.cDerivedDeclarator   
         | mk_cEnumeration          of 'a C_Ast.cEnumeration         
         | mk_cExpression           of 'a C_Ast.cExpression          
         | mk_cInitializer          of 'a C_Ast.cInitializer         
         | mk_cPartDesignator       of 'a C_Ast.cPartDesignator      
         | mk_cStatement            of 'a C_Ast.cStatement           
         | mk_cStructureUnion       of 'a C_Ast.cStructureUnion
         | mk_cTypeQualifier        of 'a C_Ast.cTypeQualifier 
         | mk_cTypeSpecifier        of 'a C_Ast.cTypeSpecifier 
         | mk_cStructTag            of C_Ast.cStructTag 
         | mk_cUnaryOp              of C_Ast.cUnaryOp  
         | mk_cAssignOp             of C_Ast.cAssignOp 
         | mk_cBinaryOp             of C_Ast.cBinaryOp 
         | mk_cIntFlag              of C_Ast.cIntFlag  
         | mk_cIntRepr              of C_Ast.cIntRepr  
         | mk_cExternalDeclaration  of 'a C_Ast.cExternalDeclaration
         | mk_cTranslationUnit      of 'a C_Ast.cTranslationUnit



  end


structure C11_Ast_Lib  : C11_AST_LIB   =
struct 
local open  C_Ast in

datatype data = data_bool of bool     | data_int of int 
              | data_string of string | data_absstring of string 

type node_content = { tag     : string,
                      sub_tag : string,
                      args    : data list }
                    
fun TT s = { tag = s, sub_tag = "", args = [] }
fun TTT s t = { tag = s, sub_tag = t, args = [] }
fun ({ tag,sub_tag,args} #>> S) = { tag = tag, sub_tag = sub_tag, args = args @ S }

fun fold_optiona _ None st = st | fold_optiona g (Some a) st = g a st;
fun fold_either g1 _ (Left a) st    = g1 a st
   |fold_either _ g2 (Right a) st   = g2 a st

fun toString_cStructTag (X:C_Ast.cStructTag) = @{make_string} X

fun toString_cIntFlag  (X:C_Ast.cIntFlag)    = @{make_string} X
                                             
fun toString_cIntRepr  (X:C_Ast.cIntRepr)    = @{make_string} X
                                             
fun toString_cUnaryOp  (X:C_Ast.cUnaryOp)    = @{make_string} X
                      
fun toString_cAssignOp (X:C_Ast.cAssignOp)   = @{make_string} X
                                             
fun toString_cBinaryOp (X:C_Ast.cBinaryOp)   = @{make_string} X
                                             
fun toString_cIntFlag  (X:C_Ast.cIntFlag)    = @{make_string} X
                                             
fun toString_cIntRepr  (X:C_Ast.cIntRepr)    = @{make_string} X

fun dark_matter x = XML.content_of (YXML.parse_body x)


fun toString_abr_string S = case  to_String_b_a_s_e S of 
                               ST X => dark_matter X
                             | STa S => map (dark_matter o Int.toString) S 
                                        |> String.concatWith "," 
                                        |> enclose "[" "]"
 
fun toString_nodeinfo (NodeInfo0 (positiona, (positiona', i), namea)) =
    let val Position0 (i1,abrS,i2,i3) = positiona;
        val Position0 (i1',abrS',i2',i3') = positiona';
        val Name0 X = namea;
    in  "<"^Int.toString i1^" : "^toString_abr_string abrS^" : "
        ^ Int.toString i2 ^" : " ^ Int.toString i3 ^ " : " ^ 
        Int.toString i1'^" : "^toString_abr_string abrS'^" : "
        ^ Int.toString i2' ^" : " ^ Int.toString i3' ^ "|" ^ Int.toString i ^"::"
        ^ Int.toString X ^ ">"
    end
   |toString_nodeinfo (OnlyPos0 (positiona, (positiona', i))) =
    let val Position0 (i1,abrS,i2,i3) = positiona;
        val Position0 (i1',abrS',i2',i3') = positiona';
    in  "<"^Int.toString i1^" : "^toString_abr_string abrS^" : "
        ^ Int.toString i2 ^" : " ^ Int.toString i3 ^ " : " ^ 
        Int.toString i1'^" : "^toString_abr_string abrS'^" : "
        ^ Int.toString i2' ^" : " ^ Int.toString i3' ^ "|" ^ Int.toString i ^ ">"
    end;
                                                       

fun toString_Chara (Chara(b1,b2,b3,b4,b5,b6,b7,b8)) = 
             let val v1 = (b1 ? (K 0)) (128)
                 val v2 = (b2 ? (K 0)) (64)
                 val v3 = (b3 ? (K 0)) (32)
                 val v4 = (b4 ? (K 0)) (16)
                 val v5 = (b5 ? (K 0)) (8)
                 val v6 = (b6 ? (K 0)) (4)
                 val v7 = (b7 ? (K 0)) (2)
                 val v8 = (b8 ? (K 0)) (1)
             in  String.implode[Char.chr(v1+v2+v3+v4+v5+v6+v7+v8)] end

(* could and should be done much more: change this on demand. *)
fun fold_cInteger g' (CInteger0 (i: int, r: cIntRepr, rfl:cIntFlag flags)) st =  
                     st |> g'(TT "CInteger0" 
                              #>> [data_int i,
                                   data_string (@{make_string} r),
                                   data_string (@{make_string} rfl)])
fun fold_cChar   g'  (CChar0(c : char, b:bool)) st          = 
                     st |> g' (TT"CChar0"
                               #>> [data_string (toString_Chara c),data_bool (b)])
  | fold_cChar   g'  (CChars0(cs : char list, b:bool)) st   = 
                     let val cs' = cs |> map toString_Chara 
                                      |> String.concat 
                     in  st |> g' (TT"CChars0" #>> [data_string cs',data_bool b]) end
fun fold_cFloat  g'  (CFloat0 (bstr: abr_string)) st          = 
                     st |> g' (TT"CChars0"#>> [data_string (@{make_string} bstr)])
fun fold_cString g' (CString0 (bstr: abr_string, b: bool)) st = 
                     st |> g' (TT"CString0"#>> [data_string (@{make_string} bstr), data_bool b])


fun fold_cConstant g (CIntConst0 (i: cInteger, a))  st = st |> fold_cInteger (fn x=>g x a) i
                                                            |> g (TT"CIntConst0") a  
  | fold_cConstant g (CCharConst0  (c : cChar, a))  st = st |> fold_cChar (fn x=>g x a) c
                                                            |> g (TT"CCharConst0") a   
  | fold_cConstant g (CFloatConst0 (f : cFloat, a)) st = st |> fold_cFloat (fn x=>g x a) f
                                                            |> g (TT"CFloatConst0") a   
  | fold_cConstant g (CStrConst0   (s : cString, a))st = st |> fold_cString (fn x=>g x a) s
                                                            |> g (TT"CStrConst0") a

fun fold_ident a g (Ident0(bstr : abr_string, i : int, ni: nodeInfo (* hack !!! *))) st = 
                   st |> g (TT "Ident0"  
                            #>> [data_string (@{make_string} bstr), 
                                 data_int i, 
                                 data_string (@{make_string} ni)
                                ]) a
(* |> fold_cString (fn x=>g x a)  *)
fun fold_cStringLiteral g (CStrLit0(cs:cString, a)) st =  st |> fold_cString (fn x=>g x a) cs
                                                             |> g (TT"CStrLit0") a 


fun  fold_cTypeSpecifier g (CAtomicType0 (decl : 'a cDeclaration, a)) st = 
                                  st |> fold_cDeclaration g decl |> g (TT"CAtomicType0") a
   | fold_cTypeSpecifier g (CBoolType0 a)     st = st |> g (TT"CBoolType0") a
   | fold_cTypeSpecifier g (CCharType0 a)     st = st |> g (TT"CCharType0") a 
   | fold_cTypeSpecifier g (CComplexType0 a)  st = st |> g (TT"CComplexType0") a 
   | fold_cTypeSpecifier g (CDoubleType0 a)   st = st |> g (TT"CDoubleType0") a 
   | fold_cTypeSpecifier g (CEnumType0(e: 'a cEnumeration, a)) st = 
                                              st |> fold_cEnumeration g e
                                                 |> g (TT"CEnumType0") a
   | fold_cTypeSpecifier g (CFloatType0 a)    st = st |> g (TT"CFloatType0") a
   | fold_cTypeSpecifier g (CInt128Type0 a)   st = st |> g (TT"CInt128Type0") a 
   | fold_cTypeSpecifier g (CIntType0 a)      st = st |> g (TT"CIntType0") a 
   | fold_cTypeSpecifier g (CLongType0 a)     st = st |> g (TT"CLongType0") a 
   | fold_cTypeSpecifier g (CSUType0 (su: 'a cStructureUnion, a))  st = 
                                              st |> fold_cStructureUnion g su
                                                 |> g (TT"CSUType0") a
   | fold_cTypeSpecifier g (CShortType0 a)    st = st |> g (TT"CShortType0") a 
   | fold_cTypeSpecifier g (CSignedType0 a)   st = st |> g (TT"CSignedType0") a 
   | fold_cTypeSpecifier g (CTypeDef0 (id:ident, a)) st = 
                                              st |>  fold_ident a g id
                                                 |>  g (TT"CTypeDef0") a 
   | fold_cTypeSpecifier g (CTypeOfExpr0 (ex: 'a cExpression, a)) st = 
                                              st |> fold_cExpression g ex 
                                                 |> g (TT"CTypeOfExpr0") a
   | fold_cTypeSpecifier g (CTypeOfType0 (decl: 'a cDeclaration, a)) st = 
                                              st |> fold_cDeclaration g decl 
                                                 |> g (TT"CTypeOfType0") a
   | fold_cTypeSpecifier g (CUnsigType0 a)    st = st |> g (TT"CUnsigType0") a
   | fold_cTypeSpecifier g (CVoidType0 a)     st = st |> g (TT"CVoidType0")  a


and  fold_cTypeQualifier g (CAtomicQual0 a) st = g (TT"CAtomicQual0") a st
   | fold_cTypeQualifier g (CAttrQual0 (CAttr0 (id,eL:'a cExpression list, a))) st = 
                                              st |> fold_ident a g id
                                                 |> fold(fold_cExpression g) eL
                                                 |> g (TT"CAttrQual0") a
   | fold_cTypeQualifier g (CConstQual0 a) st    = st |> g (TT"CConstQual0") a
   | fold_cTypeQualifier g (CNonnullQual0 a) st  = st |> g (TT"CNonnullQual0") a 
   | fold_cTypeQualifier g (CNullableQual0 a) st = st |> g (TT"CNullableQual0") a
   | fold_cTypeQualifier g (CRestrQual0 a) st    = st |> g (TT"CRestrQual0") a
   | fold_cTypeQualifier g (CVolatQual0 a) st    = st |> g (TT"CVolatQual0") a 

and  fold_cStatement g (CLabel0(id:ident, s:'a cStatement, 
                                aL: 'a cAttribute list, a)) st= 
                                  st |> fold_ident a g id
                                     |> fold_cStatement g s
                                     |> fold(fold_cAttribute g) aL
                                     |> g (TT"CLabel0") a 
   | fold_cStatement g (CCase0(ex: 'a cExpression, 
                               stmt: 'a cStatement, a)) st    = 
                                  st |> fold_cExpression g ex
                                     |> fold_cStatement g stmt
                                     |> g (TT"CCase0") a
   | fold_cStatement g (CCases0(ex1: 'a cExpression, 
                                ex2: 'a cExpression,
                                stmt:'a cStatement, a)) st   = 
                                  st |> fold_cExpression g ex1
                                     |> fold_cExpression g ex2
                                     |> fold_cStatement g stmt
                                     |> g (TT"CCases0") a
   | fold_cStatement g (CDefault0(stmt:'a cStatement, a)) st  = 
                                  st |> fold_cStatement g stmt
                                     |> g (TT"CDefault0") a
   | fold_cStatement g (CExpr0(ex_opt:'a cExpression optiona, a)) st = 
                                  st |> fold_optiona (fold_cExpression g) ex_opt
                                     |> g (TT"CExpr0") a
   | fold_cStatement g (CCompound0(idS : ident list, 
                                   cbiS: 'a cCompoundBlockItem list, a)) st = 
                                  st |> fold(fold_ident a g) idS
                                     |> fold(fold_cCompoundBlockItem g) cbiS
                                     |> g (TT"CCompound0") a
   | fold_cStatement g (CIf0(ex1:'a cExpression,stmt: 'a cStatement, 
                        stmt_opt: 'a cStatement optiona, a)) st = 
                                  st |> fold_cExpression g ex1
                                     |> fold_cStatement g stmt
                                     |> fold_optiona (fold_cStatement g) stmt_opt
                                     |> g (TT"CIf0") a
   | fold_cStatement g (CSwitch0(ex1:'a cExpression, 
                                 stmt: 'a cStatement, a)) st = 
                                  st |> fold_cExpression g ex1
                                     |> fold_cStatement g stmt
                                     |> g (TT"CSwitch0") a
   | fold_cStatement g (CWhile0(ex1:'a cExpression, 
                                stmt: 'a cStatement, b: bool, a)) st = 
                                  st |> fold_cExpression g ex1
                                     |> fold_cStatement g stmt
                                     |> g (TT"CWhile0" #>> [data_bool b]) a
   | fold_cStatement g (CFor0(ex0:('a cExpression optiona, 'a cDeclaration) either, 
                              ex1_opt: 'a cExpression optiona, 
                              ex2_opt: 'a cExpression optiona,
                              stmt: 'a cStatement, a)) st = 
                                  st |> fold_either (fold_optiona (fold_cExpression g)) 
                                                    (fold_cDeclaration g) ex0
                                     |> fold_optiona (fold_cExpression g) ex1_opt
                                     |> fold_optiona (fold_cExpression g) ex2_opt
                                     |> fold_cStatement g stmt
                                     |> g (TT"CFor0") a
   | fold_cStatement g (CGoto0(id: ident, a)) st = 
                                  st |>  fold_ident a g id
                                     |> g (TT"CGoto0") a
   | fold_cStatement g (CGotoPtr0(ex1:'a cExpression, a)) st = 
                                  st |> fold_cExpression g ex1 |> g (TT"CGotoPtr0") a
   | fold_cStatement g (CCont0 a)  st = st |> g (TT"CCont0") a
   | fold_cStatement g (CBreak0 a) st = st |> g (TT"CBreak0") a
   | fold_cStatement g (CReturn0 (ex:'a cExpression optiona,a)) st = 
                                  st |> fold_optiona (fold_cExpression g) ex |> g (TT"CReturn0") a
   | fold_cStatement g (CAsm0(_: 'a cAssemblyStatement, a)) st = 
                                  (* assembly ignored so far *)
                                  st |> g (TT"CAsm0") a

and fold_cExpression g (CComma0 (eL:'a cExpression list, a)) st = 
                                 st |> fold(fold_cExpression g) eL |> g (TT"CComma0") a
  | fold_cExpression g (CAssign0(aop:cAssignOp, 
                                 ex1:'a cExpression,
                                 ex2:'a cExpression,a)) st = 
                                  st |> fold_cExpression g ex1
                                     |> fold_cExpression g ex2 
                                     |> g (TTT"CAssign0" (toString_cAssignOp aop)) a
  | fold_cExpression g (CCond0(  ex1:'a cExpression, 
                                 ex2opt: 'a cExpression optiona, (* bescheuert ! Wieso option ?*) 
                                 ex3: 'a cExpression,a)) st = 
                                  st |> fold_cExpression g ex1 
                                     |> fold_optiona (fold_cExpression g) ex2opt
                                     |> fold_cExpression g ex3 |> g (TT"CCond0") a
  | fold_cExpression g (CBinary0(bop: cBinaryOp, ex1: 'a cExpression,ex2: 'a cExpression, a)) st =
                                  st |> fold_cExpression g ex1 
                                     |> fold_cExpression g ex2 
                                     |> g (TTT"CBinary0"(toString_cBinaryOp bop)) a 
  | fold_cExpression g (CCast0(decl:'a cDeclaration, ex: 'a cExpression, a)) st = 
                                  st |> fold_cExpression g ex 
                                     |> fold_cDeclaration g decl
                                     |> g (TT"CCast0") a
  | fold_cExpression g (CUnary0(unop:cUnaryOp, ex: 'a cExpression, a)) st = 
                                  st |> fold_cExpression g ex 
                                     |> g (TT("CUnary0 "^toString_cUnaryOp unop)) a
  | fold_cExpression g (CSizeofExpr0(ex:'a cExpression, a)) st = 
                                  st |> fold_cExpression g ex    |> g (TT"CSizeofExpr0") a
  | fold_cExpression g (CSizeofType0(decl:'a cDeclaration,a)) st = 
                                  st |> fold_cDeclaration g decl |> g (TT"CSizeofType0") a
  | fold_cExpression g (CAlignofExpr0(ex:'a cExpression, a)) st = 
                                  st |> fold_cExpression g ex    |> g (TT"CAlignofExpr0") a
  | fold_cExpression g (CAlignofType0(decl:'a cDeclaration, a)) st = 
                                  st |> fold_cDeclaration g decl |> g (TT"CAlignofType0") a
  | fold_cExpression g (CComplexReal0(ex:'a cExpression, a)) st = 
                                  st |> fold_cExpression g ex |> g (TT"CComplexReal0") a
  | fold_cExpression g (CComplexImag0(ex:'a cExpression, a)) st = 
                                  st |> fold_cExpression g ex |> g (TT"CComplexImag0") a
  | fold_cExpression g (CIndex0(ex1:'a cExpression, ex2: 'a cExpression, a)) st =
                                  st |> fold_cExpression g ex1 
                                     |> fold_cExpression g ex2 
                                     |> g (TT"CIndex0") a
  | fold_cExpression g (CCall0(ex:'a cExpression, argS: 'a cExpression list, a)) st =
                                  st |> fold_cExpression g ex 
                                     |> fold (fold_cExpression g) argS 
                                     |> g (TT"CCall0") a
  | fold_cExpression g (CMember0(ex:'a cExpression, id:ident, b, a)) st =
                                  st |> fold_cExpression g ex 
                                     |> fold_ident a g id
                                     |> g (TT"CMember0"#>> [data_bool b]) a 
  | fold_cExpression g (CVar0(id:ident,a)) st = st |> fold_ident a g id |> g (TT"CVar0") a
  | fold_cExpression g (CConst0(cc:'a cConstant)) st  = st |> fold_cConstant g cc
  | fold_cExpression g (CCompoundLit0(decl:'a cDeclaration,
                                      eqn: ('a cPartDesignator list * 'a cInitializer) list, a)) st =
                                  st |> fold(fn(S,init) => 
                                             fn st => st |> fold(fold_cPartDesignator g) S
                                                         |> fold_cInitializer g init) eqn 
                                     |> fold_cDeclaration g decl 
                                     |> g (TT"CCompoundLit0") a 
  | fold_cExpression g (CGenericSelection0(ex:'a cExpression, 
                                           eqn: ('a cDeclaration optiona*'a cExpression)list,a)) st =
                                  st |> fold_cExpression g ex 
                                     |> fold (fn (d,ex) => 
                                              fn st => st |> fold_optiona (fold_cDeclaration g) d  
                                                          |> fold_cExpression g ex) eqn  
                                     |> g (TT"CGenericSelection0") a  
  | fold_cExpression g (CStatExpr0(stmt: 'a cStatement,a)) st =  
                                  st |> fold_cStatement g stmt |> g (TT"CStatExpr0") a
  | fold_cExpression g (CLabAddrExpr0(id:ident,a)) st = 
                                  st |> fold_ident a g id |> g (TT"CLabAddrExpr0") a 
  | fold_cExpression g (CBuiltinExpr0(X: 'a cBuiltinThing)) st = st |> fold_cBuiltinThing g X
  
and fold_cDeclaration g (CDecl0(dsS : 'a cDeclarationSpecifier list, 
                                mkS: (('a cDeclarator optiona       
                                       *'a cInitializer optiona) 
                                     * 'a cExpression optiona) list,
                                a)) st = 
                                  st |> fold(fold_cDeclarationSpecifier g) dsS 
                                     |> fold(fn ((d_o, init_o),ex_opt) =>
                                             fn st => st |> fold_optiona(fold_cDeclarator g) d_o
                                                         |> fold_optiona(fold_cInitializer g) init_o
                                                         |> fold_optiona(fold_cExpression g) ex_opt) mkS
                                    |> g (TT"CDecl0") a
  | fold_cDeclaration g (CStaticAssert0(ex:'a cExpression, slit: 'a cStringLiteral, a)) st = 
                                  st |> fold_cExpression g ex 
                                     |> fold_cStringLiteral g slit
                                     |> g (TT"CStaticAssert0") a

and fold_cBuiltinThing g (CBuiltinVaArg0(ex:'a cExpression,decl: 'a cDeclaration,a)) st = 
                                  st |> fold_cExpression g ex 
                                     |> fold_cDeclaration g decl
                                     |> g (TT"CBuiltinVaArg0") a 
  | fold_cBuiltinThing g (CBuiltinOffsetOf0(d: 'a cDeclaration, _: 'a cPartDesignator list, a)) st = 
                                  st |> fold_cDeclaration g d 
                                     |> g (TT"CBuiltinOffsetOf0") a 
  | fold_cBuiltinThing g (CBuiltinTypesCompatible0 (d1: 'a cDeclaration, d2: 'a cDeclaration,a)) st= 
                                  st |> fold_cDeclaration g d1
                                     |> fold_cDeclaration g d2 
                                     |> g (TT"CBuiltinTypesCompatible0") a 

and  fold_cInitializer g (CInitExpr0(ex: 'a cExpression, a)) st = 
                                  st |> fold_cExpression g ex |> g (TT"CInitExpr0") a 
   | fold_cInitializer g (CInitList0 (mms: ('a cPartDesignator list * 'a cInitializer) list,a)) st = 
                                  st |> fold(fn (a,b) => 
                                             fn st => st|> fold(fold_cPartDesignator g) a 
                                                        |> fold_cInitializer g b) mms
                                     |> g (TT"CInitList0") a

and  fold_cPartDesignator g (CArrDesig0(ex: 'a cExpression, a)) st = 
                                  st |> fold_cExpression g ex |> g (TT"CArrDesig0") a 
   | fold_cPartDesignator g (CMemberDesig0(id: ident, a)) st = 
                                  st |> fold_ident a g id |> g (TT"CMemberDesig0") a 
   | fold_cPartDesignator g (CRangeDesig0(ex1: 'a cExpression, ex2: 'a cExpression, a)) st = 
                                  st |> fold_cExpression g ex1
                                     |> fold_cExpression g ex2
                                     |> g (TT"CRangeDesig0") a 

and fold_cAttribute g (CAttr0(id: ident, exS: 'a cExpression list, a)) st =
                                  st |> fold_ident a g id
                                     |> fold(fold_cExpression g) exS 
                                     |> g (TT"CAttr0") a 

and fold_cEnumeration g (CEnum0 (ident_opt: ident optiona,
                              exS_opt: ((ident * 'a cExpression optiona) list) optiona,
                              attrS: 'a cAttribute list, a)) st = 
                                  st |> fold_optiona(fold_ident a g) ident_opt
                                     |> fold_optiona(fold(
                                             fn (id,ex_o) =>
                                             fn st => st |> fold_ident a g id
                                                         |> fold_optiona (fold_cExpression g) ex_o)) 
                                                      exS_opt   
                                     |> fold(fold_cAttribute g) attrS
                                     |> g (TT"CEnum0") a 



and fold_cArraySize a g (CNoArrSize0 (b: bool)) st = 
                                  st |> g (TT "CNoArrSize0" #>> [data_bool b]) a 
  | fold_cArraySize a g (CArrSize0 (b:bool, ex : 'a cExpression)) st = 
                                  st |> fold_cExpression g ex 
                                     |> g (TT "CNoArrSize0" #>> [data_bool b]) a 


and fold_cDerivedDeclarator g (CPtrDeclr0 (tqS: 'a cTypeQualifier list , a)) st = 
                                  st |> fold(fold_cTypeQualifier g) tqS 
                                     |> g (TT"CPtrDeclr0") a
  | fold_cDerivedDeclarator g (CArrDeclr0 (tqS:'a cTypeQualifier list, aS: 'a cArraySize,a)) st = 
                                  st |> fold(fold_cTypeQualifier g) tqS 
                                     |> fold_cArraySize a g aS 
                                     |> g (TT"CArrDeclr0") a
  | fold_cDerivedDeclarator g (CFunDeclr0 (decl_alt: (ident list, 
                                                      ('a cDeclaration list * bool)) either, 
                                           aS: 'a cAttribute list, a)) st = 
                                  st |> fold_either 
                                             (fold(fold_ident a g)) 
                                             (fn (declS,b) =>
                                              fn st => st |> fold (fold_cDeclaration g) declS
                                                          |> g (TTT "CFunDeclr0""decl_alt-Right"
                                                                #>> [data_bool b]) a) decl_alt
                                     |> fold(fold_cAttribute g) aS 
                                     |> g (TT"CFunDeclr0") a

and fold_cDeclarationSpecifier g (CStorageSpec0(CAuto0 a)) st = 
                                  st |> g (TTT"CStorageSpec0" "CAuto0") a
   |fold_cDeclarationSpecifier g (CStorageSpec0(CRegister0 a)) st = 
                                  st |> g (TTT"CStorageSpec0" "CRegister0") a
   |fold_cDeclarationSpecifier g (CStorageSpec0(CStatic0 a)) st = 
                                  st |> g (TTT"CStorageSpec0" "CStatic0") a
   |fold_cDeclarationSpecifier g (CStorageSpec0(CExtern0 a)) st = 
                                  st |> g (TTT"CStorageSpec0" "CExtern0") a
   |fold_cDeclarationSpecifier g (CStorageSpec0(CTypedef0 a)) st = 
                                  st |> g (TTT"CStorageSpec0" "CTypedef0") a
   |fold_cDeclarationSpecifier g (CStorageSpec0(CThread0 a)) st = 
                                  st |> g (TTT"CStorageSpec0" "CThread0") a

   |fold_cDeclarationSpecifier g (CTypeSpec0(CVoidType0 a)) st = 
                                  st |> g (TTT"CTypeSpec0""CVoidType0") a
   |fold_cDeclarationSpecifier g (CTypeSpec0(CCharType0 a)) st = 
                                  st |> g (TTT"CTypeSpec0""CCharType0") a
   |fold_cDeclarationSpecifier g (CTypeSpec0(CShortType0 a)) st = 
                                  st |> g (TTT"TCTypeSpec0""CShortType0") a
   |fold_cDeclarationSpecifier g (CTypeSpec0(CIntType0 a)) st = 
                                  st |> g (TTT"CTypeSpec0""CIntType0") a
   |fold_cDeclarationSpecifier g (CTypeSpec0(CLongType0 a)) st = 
                                  st |> g (TTT"CTypeSpec0""CLongType0") a
   |fold_cDeclarationSpecifier g (CTypeSpec0(CFloatType0 a)) st = 
                                  st |> g (TTT"CTypeSpec0""CFloatType0") a
   |fold_cDeclarationSpecifier g (CTypeSpec0(CDoubleType0 a)) st = 
                                  st |> g (TTT"CTypeSpec0""CDoubleType0") a
   |fold_cDeclarationSpecifier g (CTypeSpec0(CSignedType0 a)) st = 
                                  st |> g (TTT"CTypeSpec0""CSignedType0") a
   |fold_cDeclarationSpecifier g (CTypeSpec0(CUnsigType0 a)) st = 
                                  st |> g (TTT"CTypeSpec0""CUnsigType0") a
   |fold_cDeclarationSpecifier g (CTypeSpec0(CBoolType0 a)) st = 
                                  st |> g (TTT"CTypeSpec0""CBoolType0") a

   |fold_cDeclarationSpecifier g (CTypeQual0(x: 'a cTypeQualifier)) st =
                                  st |> fold_cTypeQualifier g x

   |fold_cDeclarationSpecifier g (CFunSpec0(CInlineQual0 a)) st = 
                                  st |> g (TTT"CFunSpec0""CInlineQual0") a 
   |fold_cDeclarationSpecifier g (CFunSpec0(CNoreturnQual0 a)) st = 
                                  st |> g (TTT"CFunSpec0""CNoreturnQual0") a 
 
   |fold_cDeclarationSpecifier g (CAlignSpec0(CAlignAsType0(decl,a))) st = 
                                  st |> fold_cDeclaration g decl
                                     |> g (TTT"CAlignSpec0""CAlignAsType0") a
   |fold_cDeclarationSpecifier g (CAlignSpec0(CAlignAsExpr0(ex,a))) st = 
                                  st |> fold_cExpression g ex
                                     |> g (TTT"CAlignSpec0""CAlignAsType0") a

and fold_cDeclarator g (CDeclr0(id_opt: ident optiona,
                                declS: 'a cDerivedDeclarator list,
                                sl_opt: 'a cStringLiteral optiona,
                                attrS: 'a cAttribute list, a)) st = 
                                  st |> fold_optiona(fold_ident a g) id_opt
                                     |> fold (fold_cDerivedDeclarator g) declS
                                     |> fold_optiona(fold_cStringLiteral g) sl_opt
                                     |> fold(fold_cAttribute g) attrS
                                     |> g (TT"CDeclr0") a

and fold_cFunctionDef g (CFunDef0(dspecS: 'a cDeclarationSpecifier list,
                                  dclr: 'a cDeclarator,
                                  declsS: 'a cDeclaration list,
                                  stmt: 'a cStatement, a)) st = 
                                    st |> fold(fold_cDeclarationSpecifier g) dspecS
                                       |> fold_cDeclarator g dclr
                                       |> fold(fold_cDeclaration g) declsS
                                       |> fold_cStatement g stmt
                                       |> g (TT"CFunDef0") a

and fold_cCompoundBlockItem g (CBlockStmt0 (stmt: 'a cStatement)) st = 
                                    st |> fold_cStatement g stmt 
  | fold_cCompoundBlockItem g (CBlockDecl0 (decl : 'a cDeclaration)) st = 
                                    st |> fold_cDeclaration g decl 
  | fold_cCompoundBlockItem g (CNestedFunDef0(fdef : 'a cFunctionDef)) st = 
                                    st |> fold_cFunctionDef g fdef

and fold_cStructureUnion g (CStruct0(  ct : cStructTag, id_a: ident optiona, 
                                       declS_opt : ('a cDeclaration list) optiona,
                                       aS: 'a cAttribute list, a)) st = 
                                    st |> fold_optiona (fold_ident a g) id_a
                                       |> fold_optiona (fold(fold_cDeclaration g)) declS_opt
                                       |> fold(fold_cAttribute g) aS
                                       |> g (TTT "CStruct0" (toString_cStructTag ct)) a  
and fold_cExternalDeclaration g (CDeclExt0(cd : 'a cDeclaration)) st =
                                    st |> fold_cDeclaration g cd
  | fold_cExternalDeclaration g (CFDefExt0(fd : 'a cFunctionDef)) st = 
                                    st |>  fold_cFunctionDef g fd
  | fold_cExternalDeclaration _ (CAsmExt0( _ : 'a cStringLiteral, _ : 'a)) _ = error"Inline assembler not supprted"
and fold_cTranslationUnit g (CTranslUnit0 (ceL : 'a cExternalDeclaration list, a : 'a)) st = 
                                    st |> fold(fold_cExternalDeclaration g) ceL
                                       |> g (TT"CTranslUnit0") a


(* missing 
  datatype 'a cTranslationUnit = CTranslUnit0 of 'a cExternalDeclaration list * 'a
*)


datatype 'a C11_Ast = 
           mk_cInteger              of C_Ast.cInteger         
         | mk_cStructTag            of C_Ast.cStructTag 
         | mk_cUnaryOp              of C_Ast.cUnaryOp  
         | mk_cAssignOp             of C_Ast.cAssignOp 
         | mk_cBinaryOp             of C_Ast.cBinaryOp 
         | mk_cIntFlag              of C_Ast.cIntFlag  
         | mk_cIntRepr              of C_Ast.cIntRepr  
         | mk_cConstant             of 'a C_Ast.cConstant      
         | mk_cStringLiteral        of 'a C_Ast.cStringLiteral 
         | mk_cArraySize            of 'a C_Ast.cArraySize     
         | mk_cAttribute            of 'a C_Ast.cAttribute     
         | mk_cBuiltinThing         of 'a C_Ast.cBuiltinThing  
         | mk_cCompoundBlockItem    of 'a C_Ast.cCompoundBlockItem   
         | mk_cDeclaration          of 'a C_Ast.cDeclaration         
         | mk_cDeclarationSpecifier of 'a C_Ast.cDeclarationSpecifier
         | mk_cDeclarator           of 'a C_Ast.cDeclarator          
         | mk_cDerivedDeclarator    of 'a C_Ast.cDerivedDeclarator   
         | mk_cEnumeration          of 'a C_Ast.cEnumeration         
         | mk_cExpression           of 'a C_Ast.cExpression          
         | mk_cInitializer          of 'a C_Ast.cInitializer         
         | mk_cPartDesignator       of 'a C_Ast.cPartDesignator      
         | mk_cStatement            of 'a C_Ast.cStatement           
         | mk_cStructureUnion       of 'a C_Ast.cStructureUnion
         | mk_cTypeQualifier        of 'a C_Ast.cTypeQualifier 
         | mk_cTypeSpecifier        of 'a C_Ast.cTypeSpecifier 
         | mk_cExternalDeclaration  of 'a C_Ast.cExternalDeclaration
         | mk_cTranslationUnit      of 'a C_Ast.cTranslationUnit


end

end (*struct *)
\<close>

end
