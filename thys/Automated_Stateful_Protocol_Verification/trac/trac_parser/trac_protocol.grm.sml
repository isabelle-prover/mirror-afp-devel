 (***** GENERATED FILE -- DO NOT EDIT ****)
functor TracTransactionLrValsFun(structure Token : TOKEN)
 : sig structure ParserData : PARSER_DATA
       structure Tokens : TracTransaction_TOKENS
   end
 = 
struct
structure ParserData=
struct
structure Header = 
struct
(* SPDX-License-Identifier: BSD-3-Clause *)
open Trac_Term
 
exception NotYetSupported of string 



end
structure LrTable = Token.LrTable
structure Token = Token
local open LrTable in 
val table=let val actionRows =
"\
\\001\000\001\000\000\000\000\000\
\\001\000\001\000\098\001\003\000\098\001\017\000\098\001\018\000\113\001\
\\019\000\098\001\020\000\098\001\022\000\098\001\037\000\098\001\
\\040\000\098\001\041\000\098\001\042\000\098\001\043\000\098\001\
\\044\000\098\001\045\000\098\001\046\000\098\001\047\000\098\001\
\\048\000\098\001\052\000\098\001\053\000\098\001\054\000\098\001\
\\055\000\098\001\056\000\098\001\057\000\098\001\058\000\098\001\
\\059\000\098\001\060\000\098\001\062\000\098\001\063\000\098\001\
\\066\000\098\001\068\000\098\001\069\000\098\001\000\000\
\\001\000\001\000\099\001\002\000\114\000\003\000\099\001\017\000\099\001\
\\018\000\114\001\019\000\099\001\020\000\099\001\022\000\099\001\
\\037\000\099\001\040\000\099\001\041\000\099\001\042\000\099\001\
\\043\000\099\001\044\000\099\001\045\000\099\001\046\000\099\001\
\\047\000\099\001\048\000\099\001\052\000\099\001\053\000\099\001\
\\054\000\099\001\055\000\099\001\056\000\099\001\057\000\099\001\
\\058\000\099\001\059\000\099\001\060\000\099\001\062\000\099\001\
\\063\000\099\001\066\000\099\001\068\000\099\001\069\000\099\001\000\000\
\\001\000\002\000\076\000\000\000\
\\001\000\002\000\086\000\000\000\
\\001\000\003\000\136\000\062\000\032\000\000\000\
\\001\000\003\000\183\000\000\000\
\\001\000\003\000\189\000\000\000\
\\001\000\003\000\200\000\000\000\
\\001\000\003\000\237\000\000\000\
\\001\000\003\000\238\000\000\000\
\\001\000\003\000\245\000\000\000\
\\001\000\003\000\246\000\000\000\
\\001\000\004\000\152\000\024\000\151\000\062\000\032\000\063\000\031\000\000\000\
\\001\000\005\000\222\000\000\000\
\\001\000\008\000\005\000\000\000\
\\001\000\008\000\018\000\000\000\
\\001\000\008\000\019\000\000\000\
\\001\000\008\000\021\000\000\000\
\\001\000\008\000\022\000\000\000\
\\001\000\008\000\023\000\000\000\
\\001\000\008\000\024\000\000\000\
\\001\000\008\000\025\000\000\000\
\\001\000\008\000\177\000\000\000\
\\001\000\017\000\102\001\019\000\076\001\040\000\076\001\041\000\076\001\
\\042\000\076\001\043\000\102\001\044\000\102\001\045\000\076\001\
\\046\000\076\001\047\000\076\001\048\000\076\001\053\000\102\001\
\\062\000\076\001\063\000\076\001\066\000\076\001\000\000\
\\001\000\017\000\112\000\043\000\111\000\044\000\110\000\053\000\109\000\000\000\
\\001\000\017\000\112\000\043\000\170\000\044\000\169\000\053\000\168\000\000\000\
\\001\000\017\000\112\000\044\000\195\000\000\000\
\\001\000\017\000\244\000\000\000\
\\001\000\018\000\081\000\000\000\
\\001\000\018\000\113\000\000\000\
\\001\000\019\000\107\000\000\000\
\\001\000\019\000\137\000\000\000\
\\001\000\021\000\139\000\000\000\
\\001\000\021\000\165\000\000\000\
\\001\000\022\000\186\000\062\000\032\000\000\000\
\\001\000\022\000\199\000\062\000\032\000\063\000\031\000\000\000\
\\001\000\022\000\216\000\000\000\
\\001\000\022\000\227\000\000\000\
\\001\000\025\000\004\000\000\000\
\\001\000\040\000\074\000\041\000\073\000\042\000\072\000\045\000\071\000\
\\046\000\070\000\047\000\069\000\048\000\068\000\052\000\080\000\
\\062\000\032\000\063\000\031\000\066\000\067\000\000\000\
\\001\000\040\000\074\000\041\000\073\000\042\000\072\000\045\000\071\000\
\\046\000\070\000\047\000\069\000\048\000\068\000\062\000\032\000\
\\063\000\031\000\066\000\067\000\000\000\
\\001\000\040\000\122\000\041\000\121\000\042\000\120\000\045\000\119\000\
\\046\000\118\000\062\000\032\000\063\000\031\000\000\000\
\\001\000\049\000\090\000\050\000\089\000\000\000\
\\001\000\049\000\154\000\000\000\
\\001\000\051\000\083\000\057\000\082\000\000\000\
\\001\000\052\000\093\000\000\000\
\\001\000\052\000\181\000\000\000\
\\001\000\052\000\207\000\000\000\
\\001\000\057\000\188\000\000\000\
\\001\000\062\000\008\000\063\000\007\000\000\000\
\\001\000\062\000\032\000\000\000\
\\001\000\062\000\032\000\063\000\031\000\000\000\
\\001\000\062\000\032\000\063\000\031\000\064\000\226\000\000\000\
\\001\000\062\000\032\000\063\000\031\000\064\000\239\000\000\000\
\\001\000\062\000\141\000\000\000\
\\001\000\062\000\145\000\000\000\
\\001\000\062\000\211\000\063\000\210\000\000\000\
\\001\000\062\000\233\000\000\000\
\\001\000\062\000\249\000\000\000\
\\001\000\063\000\031\000\000\000\
\\001\000\063\000\037\000\000\000\
\\001\000\063\000\041\000\000\000\
\\001\000\065\000\147\000\000\000\
\\252\000\000\000\
\\253\000\000\000\
\\254\000\000\000\
\\255\000\000\000\
\\000\001\000\000\
\\001\001\000\000\
\\002\001\000\000\
\\003\001\000\000\
\\004\001\000\000\
\\005\001\000\000\
\\006\001\037\000\017\000\054\000\016\000\055\000\015\000\056\000\014\000\
\\058\000\013\000\059\000\012\000\060\000\011\000\000\000\
\\007\001\023\000\191\000\000\000\
\\008\001\000\000\
\\009\001\052\000\093\000\062\000\032\000\063\000\031\000\000\000\
\\009\001\062\000\032\000\063\000\031\000\000\000\
\\010\001\000\000\
\\011\001\062\000\032\000\063\000\031\000\000\000\
\\012\001\000\000\
\\013\001\000\000\
\\014\001\000\000\
\\015\001\000\000\
\\016\001\062\000\032\000\063\000\031\000\000\000\
\\017\001\000\000\
\\018\001\000\000\
\\019\001\000\000\
\\020\001\000\000\
\\021\001\000\000\
\\022\001\038\000\055\000\039\000\054\000\000\000\
\\023\001\000\000\
\\024\001\000\000\
\\025\001\063\000\031\000\000\000\
\\026\001\000\000\
\\027\001\008\000\224\000\000\000\
\\028\001\000\000\
\\029\001\063\000\041\000\000\000\
\\030\001\000\000\
\\031\001\000\000\
\\032\001\000\000\
\\033\001\000\000\
\\034\001\020\000\190\000\000\000\
\\035\001\000\000\
\\036\001\000\000\
\\037\001\020\000\187\000\000\000\
\\038\001\000\000\
\\039\001\067\000\020\000\000\000\
\\040\001\000\000\
\\041\001\062\000\032\000\063\000\031\000\000\000\
\\042\001\000\000\
\\043\001\000\000\
\\044\001\000\000\
\\045\001\020\000\242\000\000\000\
\\046\001\000\000\
\\047\001\000\000\
\\048\001\027\000\215\000\000\000\
\\049\001\000\000\
\\050\001\000\000\
\\051\001\000\000\
\\054\001\000\000\
\\055\001\000\000\
\\056\001\000\000\
\\057\001\000\000\
\\058\001\000\000\
\\059\001\000\000\
\\060\001\069\000\106\000\000\000\
\\061\001\000\000\
\\062\001\000\000\
\\063\001\000\000\
\\064\001\000\000\
\\065\001\000\000\
\\066\001\000\000\
\\067\001\000\000\
\\068\001\000\000\
\\069\001\000\000\
\\070\001\000\000\
\\071\001\000\000\
\\072\001\069\000\167\000\000\000\
\\073\001\000\000\
\\074\001\000\000\
\\075\001\000\000\
\\077\001\000\000\
\\078\001\040\000\074\000\041\000\073\000\042\000\072\000\045\000\071\000\
\\046\000\070\000\047\000\069\000\048\000\068\000\062\000\032\000\
\\063\000\031\000\066\000\067\000\000\000\
\\079\001\000\000\
\\080\001\000\000\
\\081\001\002\000\230\000\000\000\
\\082\001\000\000\
\\083\001\020\000\247\000\000\000\
\\084\001\000\000\
\\085\001\020\000\178\000\000\000\
\\086\001\000\000\
\\087\001\000\000\
\\088\001\020\000\176\000\000\000\
\\089\001\000\000\
\\090\001\008\000\177\000\000\000\
\\091\001\000\000\
\\092\001\002\000\196\000\000\000\
\\092\001\002\000\197\000\000\000\
\\092\001\002\000\228\000\000\000\
\\093\001\000\000\
\\094\001\068\000\105\000\000\000\
\\095\001\000\000\
\\096\001\000\000\
\\097\001\000\000\
\\100\001\000\000\
\\101\001\000\000\
\\102\001\000\000\
\\103\001\020\000\182\000\000\000\
\\104\001\000\000\
\\105\001\000\000\
\\106\001\000\000\
\\107\001\000\000\
\\108\001\000\000\
\\109\001\020\000\223\000\000\000\
\\110\001\000\000\
\\111\001\020\000\217\000\000\000\
\\112\001\000\000\
\\113\001\000\000\
\\114\001\000\000\
\\115\001\000\000\
\\116\001\000\000\
\\117\001\000\000\
\\118\001\000\000\
\\119\001\000\000\
\\120\001\062\000\032\000\063\000\031\000\000\000\
\\121\001\000\000\
\"
val actionRowNumbers =
"\039\000\064\000\015\000\050\000\
\\074\000\172\000\171\000\016\000\
\\065\000\017\000\108\000\018\000\
\\019\000\020\000\021\000\022\000\
\\052\000\052\000\061\000\062\000\
\\052\000\052\000\052\000\091\000\
\\041\000\074\000\003\000\180\000\
\\179\000\174\000\173\000\074\000\
\\186\000\040\000\029\000\109\000\
\\045\000\098\000\074\000\004\000\
\\085\000\074\000\043\000\074\000\
\\080\000\046\000\074\000\074\000\
\\077\000\091\000\091\000\074\000\
\\060\000\060\000\024\000\162\000\
\\127\000\031\000\144\000\143\000\
\\025\000\166\000\030\000\002\000\
\\001\000\042\000\132\000\051\000\
\\052\000\052\000\052\000\052\000\
\\052\000\072\000\005\000\073\000\
\\187\000\032\000\052\000\033\000\
\\055\000\052\000\099\000\071\000\
\\056\000\086\000\069\000\063\000\
\\063\000\067\000\081\000\013\000\
\\068\000\066\000\079\000\078\000\
\\089\000\090\000\070\000\094\000\
\\093\000\044\000\092\000\052\000\
\\051\000\110\000\145\000\052\000\
\\060\000\060\000\052\000\034\000\
\\052\000\168\000\139\000\026\000\
\\052\000\052\000\052\000\052\000\
\\052\000\131\000\157\000\154\000\
\\156\000\151\000\060\000\060\000\
\\047\000\122\000\169\000\121\000\
\\006\000\023\000\118\000\185\000\
\\184\000\035\000\100\000\106\000\
\\105\000\049\000\007\000\103\000\
\\088\000\181\000\087\000\083\000\
\\075\000\084\000\060\000\095\000\
\\063\000\163\000\027\000\128\000\
\\111\000\123\000\165\000\158\000\
\\125\000\159\000\164\000\036\000\
\\008\000\051\000\052\000\060\000\
\\060\000\060\000\060\000\048\000\
\\134\000\133\000\051\000\057\000\
\\051\000\130\000\129\000\052\000\
\\052\000\117\000\037\000\177\000\
\\182\000\055\000\055\000\102\000\
\\056\000\052\000\014\000\175\000\
\\096\000\060\000\053\000\052\000\
\\038\000\119\000\167\000\140\000\
\\135\000\160\000\137\000\142\000\
\\141\000\052\000\155\000\153\000\
\\147\000\146\000\152\000\124\000\
\\170\000\058\000\183\000\051\000\
\\107\000\101\000\104\000\076\000\
\\082\000\060\000\057\000\009\000\
\\010\000\120\000\054\000\136\000\
\\057\000\116\000\114\000\028\000\
\\178\000\176\000\097\000\161\000\
\\126\000\011\000\012\000\149\000\
\\058\000\113\000\059\000\138\000\
\\148\000\057\000\115\000\112\000\
\\150\000\000\000"
val gotoT =
"\
\\001\000\249\000\007\000\001\000\000\000\
\\000\000\
\\000\000\
\\002\000\004\000\000\000\
\\008\000\008\000\023\000\007\000\000\000\
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
\\004\000\028\000\005\000\027\000\006\000\026\000\024\000\025\000\
\\041\000\024\000\000\000\
\\004\000\028\000\005\000\027\000\006\000\034\000\051\000\033\000\
\\052\000\032\000\053\000\031\000\000\000\
\\000\000\
\\022\000\038\000\025\000\037\000\026\000\036\000\000\000\
\\004\000\028\000\005\000\027\000\006\000\042\000\015\000\041\000\
\\016\000\040\000\000\000\
\\004\000\028\000\005\000\027\000\006\000\045\000\010\000\044\000\
\\011\000\043\000\000\000\
\\004\000\028\000\005\000\027\000\006\000\048\000\010\000\044\000\
\\011\000\047\000\012\000\046\000\000\000\
\\017\000\051\000\020\000\050\000\021\000\049\000\000\000\
\\004\000\064\000\005\000\063\000\006\000\062\000\030\000\061\000\
\\031\000\060\000\034\000\059\000\036\000\058\000\037\000\057\000\
\\048\000\056\000\049\000\055\000\050\000\054\000\000\000\
\\008\000\073\000\023\000\007\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\008\000\075\000\023\000\007\000\000\000\
\\004\000\028\000\005\000\027\000\006\000\034\000\051\000\033\000\
\\052\000\032\000\053\000\076\000\000\000\
\\004\000\064\000\005\000\063\000\006\000\062\000\030\000\061\000\
\\031\000\060\000\034\000\059\000\036\000\058\000\037\000\077\000\
\\048\000\056\000\049\000\055\000\050\000\054\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\022\000\082\000\025\000\037\000\026\000\036\000\000\000\
\\008\000\083\000\023\000\007\000\000\000\
\\000\000\
\\004\000\028\000\005\000\027\000\006\000\042\000\015\000\085\000\
\\016\000\040\000\000\000\
\\008\000\086\000\023\000\007\000\000\000\
\\000\000\
\\008\000\089\000\023\000\007\000\000\000\
\\004\000\028\000\005\000\027\000\006\000\045\000\010\000\044\000\
\\011\000\090\000\000\000\
\\000\000\
\\008\000\092\000\023\000\007\000\000\000\
\\008\000\093\000\023\000\007\000\000\000\
\\004\000\028\000\005\000\027\000\006\000\095\000\012\000\094\000\000\000\
\\017\000\096\000\020\000\050\000\021\000\049\000\000\000\
\\017\000\097\000\020\000\050\000\021\000\049\000\000\000\
\\008\000\098\000\023\000\007\000\000\000\
\\005\000\101\000\018\000\100\000\019\000\099\000\000\000\
\\005\000\101\000\018\000\102\000\019\000\099\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\004\000\064\000\005\000\063\000\006\000\062\000\030\000\061\000\
\\031\000\060\000\034\000\059\000\036\000\058\000\037\000\106\000\
\\048\000\056\000\049\000\055\000\050\000\054\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\004\000\064\000\005\000\063\000\006\000\062\000\030\000\061\000\
\\031\000\115\000\048\000\114\000\049\000\055\000\050\000\113\000\000\000\
\\000\000\
\\004\000\125\000\044\000\124\000\045\000\123\000\046\000\122\000\
\\047\000\121\000\000\000\
\\004\000\064\000\005\000\063\000\006\000\062\000\030\000\061\000\
\\031\000\126\000\050\000\113\000\000\000\
\\004\000\064\000\005\000\063\000\006\000\062\000\030\000\061\000\
\\031\000\127\000\050\000\113\000\000\000\
\\004\000\064\000\005\000\063\000\006\000\062\000\030\000\061\000\
\\031\000\128\000\050\000\113\000\000\000\
\\004\000\064\000\005\000\063\000\006\000\062\000\030\000\061\000\
\\031\000\130\000\032\000\129\000\050\000\113\000\000\000\
\\004\000\064\000\005\000\063\000\006\000\062\000\030\000\061\000\
\\031\000\130\000\032\000\131\000\050\000\113\000\000\000\
\\000\000\
\\004\000\125\000\044\000\133\000\045\000\123\000\046\000\132\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\004\000\064\000\005\000\063\000\006\000\062\000\030\000\061\000\
\\031\000\136\000\050\000\113\000\000\000\
\\000\000\
\\029\000\138\000\000\000\
\\004\000\064\000\005\000\063\000\006\000\062\000\028\000\141\000\
\\030\000\061\000\031\000\130\000\032\000\140\000\050\000\113\000\000\000\
\\000\000\
\\000\000\
\\027\000\142\000\000\000\
\\000\000\
\\000\000\
\\003\000\144\000\000\000\
\\003\000\146\000\000\000\
\\000\000\
\\000\000\
\\004\000\028\000\005\000\027\000\006\000\148\000\009\000\147\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\004\000\028\000\005\000\027\000\006\000\095\000\012\000\094\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\005\000\101\000\018\000\151\000\019\000\099\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\004\000\064\000\005\000\063\000\006\000\062\000\030\000\061\000\
\\031\000\154\000\048\000\153\000\049\000\055\000\050\000\113\000\000\000\
\\004\000\125\000\044\000\133\000\045\000\123\000\046\000\155\000\000\000\
\\004\000\028\000\005\000\027\000\006\000\026\000\024\000\156\000\
\\041\000\024\000\000\000\
\\000\000\
\\004\000\064\000\005\000\063\000\006\000\062\000\030\000\061\000\
\\031\000\157\000\050\000\113\000\000\000\
\\005\000\159\000\033\000\158\000\000\000\
\\005\000\161\000\033\000\160\000\000\000\
\\004\000\064\000\005\000\063\000\006\000\062\000\030\000\061\000\
\\031\000\162\000\050\000\113\000\000\000\
\\000\000\
\\004\000\064\000\005\000\063\000\006\000\062\000\030\000\061\000\
\\031\000\130\000\032\000\164\000\050\000\113\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\004\000\064\000\005\000\063\000\006\000\062\000\030\000\061\000\
\\031\000\169\000\050\000\113\000\000\000\
\\004\000\064\000\005\000\063\000\006\000\062\000\030\000\061\000\
\\031\000\170\000\050\000\113\000\000\000\
\\004\000\064\000\005\000\063\000\006\000\062\000\030\000\061\000\
\\031\000\171\000\050\000\113\000\000\000\
\\004\000\064\000\005\000\063\000\006\000\062\000\030\000\061\000\
\\031\000\130\000\032\000\172\000\050\000\113\000\000\000\
\\004\000\064\000\005\000\063\000\006\000\062\000\030\000\061\000\
\\031\000\130\000\032\000\173\000\050\000\113\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\005\000\161\000\033\000\177\000\000\000\
\\005\000\161\000\033\000\178\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\004\000\183\000\014\000\182\000\000\000\
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
\\005\000\191\000\013\000\190\000\000\000\
\\000\000\
\\003\000\192\000\000\000\
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
\\004\000\064\000\005\000\063\000\006\000\062\000\030\000\061\000\
\\031\000\130\000\032\000\196\000\050\000\113\000\000\000\
\\000\000\
\\004\000\125\000\044\000\133\000\045\000\123\000\046\000\199\000\000\000\
\\004\000\064\000\005\000\063\000\006\000\062\000\030\000\061\000\
\\031\000\200\000\050\000\113\000\000\000\
\\005\000\201\000\033\000\158\000\000\000\
\\005\000\161\000\033\000\202\000\000\000\
\\005\000\161\000\033\000\203\000\000\000\
\\005\000\161\000\033\000\204\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\004\000\125\000\044\000\133\000\045\000\123\000\046\000\206\000\000\000\
\\042\000\207\000\000\000\
\\004\000\125\000\044\000\210\000\000\000\
\\000\000\
\\000\000\
\\004\000\064\000\005\000\063\000\006\000\062\000\030\000\061\000\
\\031\000\211\000\050\000\113\000\000\000\
\\004\000\064\000\005\000\063\000\006\000\062\000\030\000\061\000\
\\031\000\130\000\032\000\212\000\050\000\113\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\029\000\216\000\000\000\
\\029\000\217\000\000\000\
\\000\000\
\\027\000\218\000\000\000\
\\004\000\028\000\005\000\027\000\006\000\148\000\009\000\219\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\005\000\161\000\033\000\158\000\000\000\
\\004\000\064\000\005\000\063\000\006\000\062\000\030\000\061\000\
\\031\000\130\000\032\000\223\000\050\000\113\000\000\000\
\\004\000\064\000\005\000\063\000\006\000\062\000\030\000\061\000\
\\031\000\130\000\032\000\223\000\050\000\113\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\004\000\064\000\005\000\063\000\006\000\062\000\030\000\061\000\
\\031\000\227\000\050\000\113\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\039\000\230\000\040\000\229\000\000\000\
\\000\000\
\\004\000\183\000\014\000\232\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\005\000\191\000\013\000\233\000\000\000\
\\042\000\234\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\004\000\064\000\005\000\063\000\006\000\062\000\030\000\061\000\
\\031\000\130\000\032\000\223\000\050\000\113\000\000\000\
\\000\000\
\\042\000\239\000\043\000\238\000\000\000\
\\000\000\
\\000\000\
\\038\000\241\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\039\000\230\000\040\000\246\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\042\000\239\000\043\000\248\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\"
val numstates = 250
val numrules = 126
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
          in f 0 handle General.Subscript => ()
          end
in
val entry_to_action = fn 0 => ACCEPT | 1 => ERROR | j => Array.sub(memo,(j-2))
end
val gotoT=Array.fromList(string_to_table(string_to_pairlist(NT,STATE),gotoT))
val actionRows=string_to_table(string_to_pairlist_default(T,entry_to_action),actionRows)
val actionRowNumbers = string_to_list actionRowNumbers
val actionT = let val actionRowLookUp=
let val a=Array.fromList(actionRows) in fn i=>Array.sub(a,i) end
in Array.fromList(List.map actionRowLookUp actionRowNumbers)
end
in LrTable.mkLrTable {actions=actionT,gotos=gotoT,numRules=numrules,
numStates=numstates,initialState=STATE 0}
end
end
local open Header in
type pos =  ( int * int * int ) 
type arg = unit
structure MlyValue = 
struct
datatype svalue = VOID | ntVOID of unit ->  unit
 | FORALL of unit ->  (string) | OR of unit ->  (string)
 | OF of unit ->  (string) | STAR of unit ->  (string)
 | INTEGER_LITERAL of unit ->  (string)
 | UNDERSCORE of unit ->  (string)
 | LOWER_STRING_LITERAL of unit ->  (string)
 | UPPER_STRING_LITERAL of unit ->  (string)
 | STRING_LITERAL of unit ->  (string)
 | ABBREVIATIONS of unit ->  (string)
 | TRANSACTIONS of unit ->  (string) | ANALYSIS of unit ->  (string)
 | ARROW of unit ->  (string) | SETS of unit ->  (string)
 | ENUMERATIONS of unit ->  (string) | TYPES of unit ->  (string)
 | DOUBLEEQUAL of unit ->  (string) | EQUAL of unit ->  (string)
 | QUESTION of unit ->  (string) | DOUBLESLASH of unit ->  (string)
 | SLASH of unit ->  (string) | ATTACK of unit ->  (string)
 | NEW of unit ->  (string) | DELETE of unit ->  (string)
 | INSERT of unit ->  (string) | NOTIN of unit ->  (string)
 | IN of unit ->  (string) | LET of unit ->  (string)
 | SEND of unit ->  (string) | RECEIVE of unit ->  (string)
 | PRIVATE of unit ->  (string) | PUBLIC of unit ->  (string)
 | FUNCTIONS of unit ->  (string) | Sets of unit ->  (string)
 | TBETWEEN of unit ->  (string) | TSECRET of unit ->  (string)
 | ON of unit ->  (string) | WEAKLY of unit ->  (string)
 | AUTHENTICATES of unit ->  (string) | GOALS of unit ->  (string)
 | ABSTRACTION of unit ->  (string) | ACTIONS of unit ->  (string)
 | WHERE of unit ->  (string) | KNOWLEDGE of unit ->  (string)
 | PROTOCOL of unit ->  (string) | INFINITESET of unit ->  (string)
 | UNION of unit ->  (string) | CLOSESQB of unit ->  (string)
 | OPENSQB of unit ->  (string) | COMMA of unit ->  (string)
 | DOT of unit ->  (string) | EXCLAM of unit ->  (string)
 | UNEQUAL of unit ->  (string) | PERCENT of unit ->  (string)
 | FSECCH of unit ->  (string) | FAUTHCH of unit ->  (string)
 | INSECCH of unit ->  (string) | CONFCH of unit ->  (string)
 | AUTHCH of unit ->  (string) | SECCH of unit ->  (string)
 | SEMICOLON of unit ->  (string) | COLON of unit ->  (string)
 | CLOSESCRYPT of unit ->  (string) | OPENSCRYPT of unit ->  (string)
 | CLOSEB of unit ->  (string) | OPENB of unit ->  (string)
 | CLOSEP of unit ->  (string) | OPENP of unit ->  (string)
 | abbrev_spec of unit ->  (TracProtocol.abbreviation list)
 | abbrev_decl of unit ->  (TracProtocol.abbreviation)
 | abbrev_head of unit ->  (string*string list)
 | abbrev of unit ->  (string*Trac_Term.Msg list)
 | negcheck of unit ->  (TracProtocol.Negcheck)
 | negcheck_disj of unit ->  (TracProtocol.Negcheck list)
 | vars_opts of unit ->  ( ( string list * Trac_Term.MsgType )  list)
 | vars_typs of unit ->  ( ( string list * Trac_Term.MsgType )  list)
 | vars_typ of unit ->  (string list*Trac_Term.MsgType)
 | vars of unit ->  (string list)
 | typs of unit ->  (Trac_Term.MsgType list)
 | typ of unit ->  (Trac_Term.MsgType)
 | transaction_name of unit ->  (TracProtocol.transaction_name)
 | ineqs of unit ->  ( ( string * string )  list)
 | ineq of unit ->  (string*string) | ineq_aux of unit ->  (string)
 | actions_ext of unit ->  (TracProtocol.labeled_action list)
 | action_ext of unit ->  (TracProtocol.labeled_action)
 | actions of unit ->  ( ( TracProtocol.prot_label * TracProtocol.action )  list)
 | action of unit ->  (TracProtocol.prot_label*TracProtocol.action)
 | setexp of unit ->  (string*Trac_Term.Msg list)
 | msgs of unit ->  (Trac_Term.Msg list)
 | msg of unit ->  (Trac_Term.Msg)
 | msg_atom of unit ->  (Trac_Term.Msg)
 | result of unit ->  (string list)
 | keys of unit ->  (Trac_Term.Msg list)
 | head_params of unit ->  (string list)
 | head of unit ->  (string*string list)
 | rule of unit ->  (TracProtocol.ruleT)
 | transaction_spec of unit ->  (TracProtocol.transaction list)
 | transaction_spec_head of unit ->  (string option)
 | analysis_spec of unit ->  (TracProtocol.anaT)
 | pub_fun_spec of unit ->  (TracProtocol.funT list)
 | priv_fun_spec of unit ->  (TracProtocol.funT list)
 | fun_spec of unit ->  (TracProtocol.funT)
 | fun_specs of unit ->  (TracProtocol.funT list)
 | priv_or_pub_fun_spec of unit ->  (TracProtocol.fun_spec)
 | set_spec of unit ->  (TracProtocol.set_spec_elem)
 | set_specs of unit ->  (TracProtocol.set_spec)
 | uidents of unit ->  (string list)
 | lidents of unit ->  (string list)
 | type_specs of unit ->  (string list)
 | enum_specs of unit ->  ( ( string * TracProtocol.enum_spec_elem )  list)
 | enum_spec of unit ->  ( ( string * TracProtocol.enum_spec_elem ) )
 | type_union of unit ->  ( ( string list ) )
 | protocol_spec of unit ->  (TracProtocol.protocol)
 | trac_protocol of unit ->  (TracProtocol.protocol)
 | ident of unit ->  (string) | lident of unit ->  (string)
 | uident of unit ->  (string) | arity of unit ->  (int)
 | name of unit ->  (string)
 | START of unit ->  (TracProtocol.protocol)
end
type svalue = MlyValue.svalue
type result = TracProtocol.protocol
end
structure EC=
struct
open LrTable
infix 5 $$
fun x $$ y = y::x
val is_keyword =
fn _ => false
val preferred_change : (term list * term list) list = 
nil
val noShift = 
fn (T 0) => true | _ => false
val showTerminal =
fn (T 0) => "EOF"
  | (T 1) => "OPENP"
  | (T 2) => "CLOSEP"
  | (T 3) => "OPENB"
  | (T 4) => "CLOSEB"
  | (T 5) => "OPENSCRYPT"
  | (T 6) => "CLOSESCRYPT"
  | (T 7) => "COLON"
  | (T 8) => "SEMICOLON"
  | (T 9) => "SECCH"
  | (T 10) => "AUTHCH"
  | (T 11) => "CONFCH"
  | (T 12) => "INSECCH"
  | (T 13) => "FAUTHCH"
  | (T 14) => "FSECCH"
  | (T 15) => "PERCENT"
  | (T 16) => "UNEQUAL"
  | (T 17) => "EXCLAM"
  | (T 18) => "DOT"
  | (T 19) => "COMMA"
  | (T 20) => "OPENSQB"
  | (T 21) => "CLOSESQB"
  | (T 22) => "UNION"
  | (T 23) => "INFINITESET"
  | (T 24) => "PROTOCOL"
  | (T 25) => "KNOWLEDGE"
  | (T 26) => "WHERE"
  | (T 27) => "ACTIONS"
  | (T 28) => "ABSTRACTION"
  | (T 29) => "GOALS"
  | (T 30) => "AUTHENTICATES"
  | (T 31) => "WEAKLY"
  | (T 32) => "ON"
  | (T 33) => "TSECRET"
  | (T 34) => "TBETWEEN"
  | (T 35) => "Sets"
  | (T 36) => "FUNCTIONS"
  | (T 37) => "PUBLIC"
  | (T 38) => "PRIVATE"
  | (T 39) => "RECEIVE"
  | (T 40) => "SEND"
  | (T 41) => "LET"
  | (T 42) => "IN"
  | (T 43) => "NOTIN"
  | (T 44) => "INSERT"
  | (T 45) => "DELETE"
  | (T 46) => "NEW"
  | (T 47) => "ATTACK"
  | (T 48) => "SLASH"
  | (T 49) => "DOUBLESLASH"
  | (T 50) => "QUESTION"
  | (T 51) => "EQUAL"
  | (T 52) => "DOUBLEEQUAL"
  | (T 53) => "TYPES"
  | (T 54) => "ENUMERATIONS"
  | (T 55) => "SETS"
  | (T 56) => "ARROW"
  | (T 57) => "ANALYSIS"
  | (T 58) => "TRANSACTIONS"
  | (T 59) => "ABBREVIATIONS"
  | (T 60) => "STRING_LITERAL"
  | (T 61) => "UPPER_STRING_LITERAL"
  | (T 62) => "LOWER_STRING_LITERAL"
  | (T 63) => "UNDERSCORE"
  | (T 64) => "INTEGER_LITERAL"
  | (T 65) => "STAR"
  | (T 66) => "OF"
  | (T 67) => "OR"
  | (T 68) => "FORALL"
  | _ => "bogus-term"
local open Header in
val errtermvalue=
fn _ => MlyValue.VOID
end
val terms : term list = nil
 $$ (T 0)end
structure Actions =
struct 
exception mlyAction of int
local open Header in
val actions = 
fn (i392,defaultPos,stack,
    (()):arg) =>
case (i392,stack)
of  ( 0, ( ( _, ( MlyValue.trac_protocol trac_protocol1, 
trac_protocol1left, trac_protocol1right)) :: rest671)) => let val  
result = MlyValue.START (fn _ => let val  (trac_protocol as 
trac_protocol1) = trac_protocol1 ()
 in (trac_protocol)
end)
 in ( LrTable.NT 0, ( result, trac_protocol1left, trac_protocol1right)
, rest671)
end
|  ( 1, ( ( _, ( MlyValue.protocol_spec protocol_spec1, _, 
protocol_spec1right)) :: ( _, ( MlyValue.name name1, _, _)) :: ( _, ( 
MlyValue.COLON COLON1, _, _)) :: ( _, ( MlyValue.PROTOCOL PROTOCOL1, 
PROTOCOL1left, _)) :: rest671)) => let val  result = 
MlyValue.trac_protocol (fn _ => let val  PROTOCOL1 = PROTOCOL1 ()
 val  COLON1 = COLON1 ()
 val  (name as name1) = name1 ()
 val  (protocol_spec as protocol_spec1) = protocol_spec1 ()
 in (TracProtocol.update_name protocol_spec name)
end)
 in ( LrTable.NT 6, ( result, PROTOCOL1left, protocol_spec1right), 
rest671)
end
|  ( 2, ( ( _, ( MlyValue.protocol_spec protocol_spec1, _, 
protocol_spec1right)) :: ( _, ( MlyValue.enum_specs enum_specs1, _, _)
) :: ( _, ( MlyValue.COLON COLON1, _, _)) :: ( _, ( MlyValue.TYPES 
TYPES1, TYPES1left, _)) :: rest671)) => let val  result = 
MlyValue.protocol_spec (fn _ => let val  TYPES1 = TYPES1 ()
 val  COLON1 = COLON1 ()
 val  enum_specs1 = enum_specs1 ()
 val  protocol_spec1 = protocol_spec1 ()
 in (
error "Using the name \"Types\" for the section containing the enumeration declarations is deprecated - use \"Enumerations\" instead."
)
end)
 in ( LrTable.NT 7, ( result, TYPES1left, protocol_spec1right), 
rest671)
end
|  ( 3, ( ( _, ( MlyValue.protocol_spec protocol_spec1, _, 
protocol_spec1right)) :: ( _, ( MlyValue.enum_specs enum_specs1, _, _)
) :: ( _, ( MlyValue.COLON COLON1, _, _)) :: ( _, ( 
MlyValue.ENUMERATIONS ENUMERATIONS1, ENUMERATIONS1left, _)) :: rest671
)) => let val  result = MlyValue.protocol_spec (fn _ => let val  
ENUMERATIONS1 = ENUMERATIONS1 ()
 val  COLON1 = COLON1 ()
 val  (enum_specs as enum_specs1) = enum_specs1 ()
 val  (protocol_spec as protocol_spec1) = protocol_spec1 ()
 in (TracProtocol.update_enum_spec protocol_spec enum_specs)
end)
 in ( LrTable.NT 7, ( result, ENUMERATIONS1left, protocol_spec1right),
 rest671)
end
|  ( 4, ( ( _, ( MlyValue.protocol_spec protocol_spec1, _, 
protocol_spec1right)) :: ( _, ( MlyValue.type_specs type_specs1, _, _)
) :: ( _, ( MlyValue.COLON COLON1, _, _)) :: ( _, ( MlyValue.TYPES 
TYPES1, TYPES1left, _)) :: rest671)) => let val  result = 
MlyValue.protocol_spec (fn _ => let val  TYPES1 = TYPES1 ()
 val  COLON1 = COLON1 ()
 val  (type_specs as type_specs1) = type_specs1 ()
 val  (protocol_spec as protocol_spec1) = protocol_spec1 ()
 in (TracProtocol.update_type_spec protocol_spec type_specs)
end)
 in ( LrTable.NT 7, ( result, TYPES1left, protocol_spec1right), 
rest671)
end
|  ( 5, ( ( _, ( MlyValue.protocol_spec protocol_spec1, _, 
protocol_spec1right)) :: ( _, ( MlyValue.set_specs set_specs1, _, _))
 :: ( _, ( MlyValue.COLON COLON1, _, _)) :: ( _, ( MlyValue.SETS SETS1
, SETS1left, _)) :: rest671)) => let val  result = 
MlyValue.protocol_spec (fn _ => let val  SETS1 = SETS1 ()
 val  COLON1 = COLON1 ()
 val  (set_specs as set_specs1) = set_specs1 ()
 val  (protocol_spec as protocol_spec1) = protocol_spec1 ()
 in (TracProtocol.update_sets protocol_spec set_specs)
end)
 in ( LrTable.NT 7, ( result, SETS1left, protocol_spec1right), rest671
)
end
|  ( 6, ( ( _, ( MlyValue.protocol_spec protocol_spec1, _, 
protocol_spec1right)) :: ( _, ( MlyValue.priv_or_pub_fun_spec 
priv_or_pub_fun_spec1, _, _)) :: ( _, ( MlyValue.COLON COLON1, _, _))
 :: ( _, ( MlyValue.FUNCTIONS FUNCTIONS1, FUNCTIONS1left, _)) :: 
rest671)) => let val  result = MlyValue.protocol_spec (fn _ => let
 val  FUNCTIONS1 = FUNCTIONS1 ()
 val  COLON1 = COLON1 ()
 val  (priv_or_pub_fun_spec as priv_or_pub_fun_spec1) = 
priv_or_pub_fun_spec1 ()
 val  (protocol_spec as protocol_spec1) = protocol_spec1 ()
 in (TracProtocol.update_functions protocol_spec priv_or_pub_fun_spec)

end)
 in ( LrTable.NT 7, ( result, FUNCTIONS1left, protocol_spec1right), 
rest671)
end
|  ( 7, ( ( _, ( MlyValue.protocol_spec protocol_spec1, _, 
protocol_spec1right)) :: ( _, ( MlyValue.analysis_spec analysis_spec1,
 _, _)) :: ( _, ( MlyValue.COLON COLON1, _, _)) :: ( _, ( 
MlyValue.ANALYSIS ANALYSIS1, ANALYSIS1left, _)) :: rest671)) => let
 val  result = MlyValue.protocol_spec (fn _ => let val  ANALYSIS1 = 
ANALYSIS1 ()
 val  COLON1 = COLON1 ()
 val  (analysis_spec as analysis_spec1) = analysis_spec1 ()
 val  (protocol_spec as protocol_spec1) = protocol_spec1 ()
 in (TracProtocol.update_analysis protocol_spec analysis_spec)
end)
 in ( LrTable.NT 7, ( result, ANALYSIS1left, protocol_spec1right), 
rest671)
end
|  ( 8, ( ( _, ( MlyValue.protocol_spec protocol_spec1, _, 
protocol_spec1right)) :: ( _, ( MlyValue.transaction_spec 
transaction_spec1, _, _)) :: ( _, ( MlyValue.COLON COLON1, _, _)) :: (
 _, ( MlyValue.transaction_spec_head transaction_spec_head1, 
transaction_spec_head1left, _)) :: rest671)) => let val  result = 
MlyValue.protocol_spec (fn _ => let val  (transaction_spec_head as 
transaction_spec_head1) = transaction_spec_head1 ()
 val  COLON1 = COLON1 ()
 val  (transaction_spec as transaction_spec1) = transaction_spec1 ()
 val  (protocol_spec as protocol_spec1) = protocol_spec1 ()
 in (
TracProtocol.update_transactions transaction_spec_head protocol_spec transaction_spec
)
end)
 in ( LrTable.NT 7, ( result, transaction_spec_head1left, 
protocol_spec1right), rest671)
end
|  ( 9, ( ( _, ( MlyValue.protocol_spec protocol_spec1, _, 
protocol_spec1right)) :: ( _, ( MlyValue.abbrev_spec abbrev_spec1, _,
 _)) :: ( _, ( MlyValue.COLON COLON1, _, _)) :: ( _, ( 
MlyValue.ABBREVIATIONS ABBREVIATIONS1, ABBREVIATIONS1left, _)) :: 
rest671)) => let val  result = MlyValue.protocol_spec (fn _ => let
 val  ABBREVIATIONS1 = ABBREVIATIONS1 ()
 val  COLON1 = COLON1 ()
 val  (abbrev_spec as abbrev_spec1) = abbrev_spec1 ()
 val  (protocol_spec as protocol_spec1) = protocol_spec1 ()
 in (TracProtocol.update_abbreviations protocol_spec abbrev_spec)
end)
 in ( LrTable.NT 7, ( result, ABBREVIATIONS1left, protocol_spec1right)
, rest671)
end
|  ( 10, ( rest671)) => let val  result = MlyValue.protocol_spec (fn _
 => (TracProtocol.empty))
 in ( LrTable.NT 7, ( result, defaultPos, defaultPos), rest671)
end
|  ( 11, ( ( _, ( MlyValue.ident ident1, ident1left, ident1right)) :: 
rest671)) => let val  result = MlyValue.type_union (fn _ => let val  (
ident as ident1) = ident1 ()
 in ([ident])
end)
 in ( LrTable.NT 8, ( result, ident1left, ident1right), rest671)
end
|  ( 12, ( ( _, ( MlyValue.type_union type_union1, _, type_union1right
)) :: ( _, ( MlyValue.UNION UNION1, _, _)) :: ( _, ( MlyValue.ident 
ident1, ident1left, _)) :: rest671)) => let val  result = 
MlyValue.type_union (fn _ => let val  (ident as ident1) = ident1 ()
 val  UNION1 = UNION1 ()
 val  (type_union as type_union1) = type_union1 ()
 in (ident::type_union)
end)
 in ( LrTable.NT 8, ( result, ident1left, type_union1right), rest671)

end
|  ( 13, ( ( _, ( MlyValue.ident ident1, ident1left, ident1right)) :: 
rest671)) => let val  result = MlyValue.type_specs (fn _ => let val  (
ident as ident1) = ident1 ()
 in ([ident])
end)
 in ( LrTable.NT 11, ( result, ident1left, ident1right), rest671)
end
|  ( 14, ( ( _, ( MlyValue.type_specs type_specs1, _, type_specs1right
)) :: ( _, ( MlyValue.ident ident1, ident1left, _)) :: rest671)) =>
 let val  result = MlyValue.type_specs (fn _ => let val  (ident as 
ident1) = ident1 ()
 val  (type_specs as type_specs1) = type_specs1 ()
 in (ident::type_specs)
end)
 in ( LrTable.NT 11, ( result, ident1left, type_specs1right), rest671)

end
|  ( 15, ( ( _, ( MlyValue.enum_spec enum_spec1, enum_spec1left, 
enum_spec1right)) :: rest671)) => let val  result = 
MlyValue.enum_specs (fn _ => let val  (enum_spec as enum_spec1) = 
enum_spec1 ()
 in ([enum_spec])
end)
 in ( LrTable.NT 10, ( result, enum_spec1left, enum_spec1right), 
rest671)
end
|  ( 16, ( ( _, ( MlyValue.enum_specs enum_specs1, _, enum_specs1right
)) :: ( _, ( MlyValue.enum_spec enum_spec1, enum_spec1left, _)) :: 
rest671)) => let val  result = MlyValue.enum_specs (fn _ => let val  (
enum_spec as enum_spec1) = enum_spec1 ()
 val  (enum_specs as enum_specs1) = enum_specs1 ()
 in (enum_spec::enum_specs)
end)
 in ( LrTable.NT 10, ( result, enum_spec1left, enum_specs1right), 
rest671)
end
|  ( 17, ( ( _, ( MlyValue.CLOSEB CLOSEB1, _, CLOSEB1right)) :: ( _, (
 MlyValue.lidents lidents1, _, _)) :: ( _, ( MlyValue.OPENB OPENB1, _,
 _)) :: ( _, ( MlyValue.EQUAL EQUAL1, _, _)) :: ( _, ( MlyValue.ident 
ident1, ident1left, _)) :: rest671)) => let val  result = 
MlyValue.enum_spec (fn _ => let val  (ident as ident1) = ident1 ()
 val  EQUAL1 = EQUAL1 ()
 val  OPENB1 = OPENB1 ()
 val  (lidents as lidents1) = lidents1 ()
 val  CLOSEB1 = CLOSEB1 ()
 in ((ident, TracProtocol.Consts lidents))
end)
 in ( LrTable.NT 9, ( result, ident1left, CLOSEB1right), rest671)
end
|  ( 18, ( ( _, ( MlyValue.type_union type_union1, _, type_union1right
)) :: ( _, ( MlyValue.EQUAL EQUAL1, _, _)) :: ( _, ( MlyValue.ident 
ident1, ident1left, _)) :: rest671)) => let val  result = 
MlyValue.enum_spec (fn _ => let val  (ident as ident1) = ident1 ()
 val  EQUAL1 = EQUAL1 ()
 val  (type_union as type_union1) = type_union1 ()
 in ((ident, TracProtocol.Union type_union))
end)
 in ( LrTable.NT 9, ( result, ident1left, type_union1right), rest671)

end
|  ( 19, ( ( _, ( MlyValue.INFINITESET INFINITESET1, _, 
INFINITESET1right)) :: ( _, ( MlyValue.EQUAL EQUAL1, _, _)) :: ( _, ( 
MlyValue.ident ident1, ident1left, _)) :: rest671)) => let val  result
 = MlyValue.enum_spec (fn _ => let val  (ident as ident1) = ident1 ()
 val  EQUAL1 = EQUAL1 ()
 val  INFINITESET1 = INFINITESET1 ()
 in ((ident, TracProtocol.InfiniteSet))
end)
 in ( LrTable.NT 9, ( result, ident1left, INFINITESET1right), rest671)

end
|  ( 20, ( ( _, ( MlyValue.set_spec set_spec1, set_spec1left, 
set_spec1right)) :: rest671)) => let val  result = MlyValue.set_specs
 (fn _ => let val  (set_spec as set_spec1) = set_spec1 ()
 in ([set_spec])
end)
 in ( LrTable.NT 14, ( result, set_spec1left, set_spec1right), rest671
)
end
|  ( 21, ( ( _, ( MlyValue.set_specs set_specs1, _, set_specs1right))
 :: ( _, ( MlyValue.set_spec set_spec1, set_spec1left, _)) :: rest671)
) => let val  result = MlyValue.set_specs (fn _ => let val  (set_spec
 as set_spec1) = set_spec1 ()
 val  (set_specs as set_specs1) = set_specs1 ()
 in (set_spec::set_specs)
end)
 in ( LrTable.NT 14, ( result, set_spec1left, set_specs1right), 
rest671)
end
|  ( 22, ( ( _, ( MlyValue.arity arity1, _, arity1right)) :: ( _, ( 
MlyValue.SLASH SLASH1, _, _)) :: ( _, ( MlyValue.ident ident1, 
ident1left, _)) :: rest671)) => let val  result = MlyValue.set_spec
 (fn _ => let val  (ident as ident1) = ident1 ()
 val  SLASH1 = SLASH1 ()
 val  (arity as arity1) = arity1 ()
 in ((ident, arity, false))
end)
 in ( LrTable.NT 15, ( result, ident1left, arity1right), rest671)
end
|  ( 23, ( ( _, ( MlyValue.arity arity1, _, arity1right)) :: ( _, ( 
MlyValue.DOUBLESLASH DOUBLESLASH1, _, _)) :: ( _, ( MlyValue.ident 
ident1, ident1left, _)) :: rest671)) => let val  result = 
MlyValue.set_spec (fn _ => let val  (ident as ident1) = ident1 ()
 val  DOUBLESLASH1 = DOUBLESLASH1 ()
 val  (arity as arity1) = arity1 ()
 in ((ident, arity, true))
end)
 in ( LrTable.NT 15, ( result, ident1left, arity1right), rest671)
end
|  ( 24, ( ( _, ( MlyValue.priv_or_pub_fun_spec priv_or_pub_fun_spec1,
 _, priv_or_pub_fun_spec1right)) :: ( _, ( MlyValue.pub_fun_spec 
pub_fun_spec1, pub_fun_spec1left, _)) :: rest671)) => let val  result
 = MlyValue.priv_or_pub_fun_spec (fn _ => let val  (pub_fun_spec as 
pub_fun_spec1) = pub_fun_spec1 ()
 val  (priv_or_pub_fun_spec as priv_or_pub_fun_spec1) = 
priv_or_pub_fun_spec1 ()
 in (TracProtocol.update_fun_public priv_or_pub_fun_spec pub_fun_spec)

end)
 in ( LrTable.NT 16, ( result, pub_fun_spec1left, 
priv_or_pub_fun_spec1right), rest671)
end
|  ( 25, ( ( _, ( MlyValue.priv_or_pub_fun_spec priv_or_pub_fun_spec1,
 _, priv_or_pub_fun_spec1right)) :: ( _, ( MlyValue.priv_fun_spec 
priv_fun_spec1, priv_fun_spec1left, _)) :: rest671)) => let val  
result = MlyValue.priv_or_pub_fun_spec (fn _ => let val  (
priv_fun_spec as priv_fun_spec1) = priv_fun_spec1 ()
 val  (priv_or_pub_fun_spec as priv_or_pub_fun_spec1) = 
priv_or_pub_fun_spec1 ()
 in (
TracProtocol.update_fun_private priv_or_pub_fun_spec priv_fun_spec)

end)
 in ( LrTable.NT 16, ( result, priv_fun_spec1left, 
priv_or_pub_fun_spec1right), rest671)
end
|  ( 26, ( rest671)) => let val  result = 
MlyValue.priv_or_pub_fun_spec (fn _ => (TracProtocol.fun_empty))
 in ( LrTable.NT 16, ( result, defaultPos, defaultPos), rest671)
end
|  ( 27, ( ( _, ( MlyValue.fun_specs fun_specs1, _, fun_specs1right))
 :: ( _, ( MlyValue.PUBLIC PUBLIC1, PUBLIC1left, _)) :: rest671)) =>
 let val  result = MlyValue.pub_fun_spec (fn _ => let val  PUBLIC1 = 
PUBLIC1 ()
 val  (fun_specs as fun_specs1) = fun_specs1 ()
 in (fun_specs)
end)
 in ( LrTable.NT 20, ( result, PUBLIC1left, fun_specs1right), rest671)

end
|  ( 28, ( ( _, ( MlyValue.fun_specs fun_specs1, _, fun_specs1right))
 :: ( _, ( MlyValue.PRIVATE PRIVATE1, PRIVATE1left, _)) :: rest671))
 => let val  result = MlyValue.priv_fun_spec (fn _ => let val  
PRIVATE1 = PRIVATE1 ()
 val  (fun_specs as fun_specs1) = fun_specs1 ()
 in (fun_specs)
end)
 in ( LrTable.NT 19, ( result, PRIVATE1left, fun_specs1right), rest671
)
end
|  ( 29, ( ( _, ( MlyValue.fun_spec fun_spec1, fun_spec1left, 
fun_spec1right)) :: rest671)) => let val  result = MlyValue.fun_specs
 (fn _ => let val  (fun_spec as fun_spec1) = fun_spec1 ()
 in ([fun_spec])
end)
 in ( LrTable.NT 17, ( result, fun_spec1left, fun_spec1right), rest671
)
end
|  ( 30, ( ( _, ( MlyValue.fun_specs fun_specs1, _, fun_specs1right))
 :: ( _, ( MlyValue.fun_spec fun_spec1, fun_spec1left, _)) :: rest671)
) => let val  result = MlyValue.fun_specs (fn _ => let val  (fun_spec
 as fun_spec1) = fun_spec1 ()
 val  (fun_specs as fun_specs1) = fun_specs1 ()
 in (fun_spec::fun_specs)
end)
 in ( LrTable.NT 17, ( result, fun_spec1left, fun_specs1right), 
rest671)
end
|  ( 31, ( ( _, ( MlyValue.arity arity1, _, arity1right)) :: ( _, ( 
MlyValue.SLASH SLASH1, _, _)) :: ( _, ( MlyValue.lident lident1, 
lident1left, _)) :: rest671)) => let val  result = MlyValue.fun_spec
 (fn _ => let val  (lident as lident1) = lident1 ()
 val  SLASH1 = SLASH1 ()
 val  (arity as arity1) = arity1 ()
 in ((lident, arity, NONE))
end)
 in ( LrTable.NT 18, ( result, lident1left, arity1right), rest671)
end
|  ( 32, ( ( _, ( MlyValue.typ typ1, _, typ1right)) :: ( _, ( 
MlyValue.COLON COLON1, _, _)) :: ( _, ( MlyValue.arity arity1, _, _))
 :: ( _, ( MlyValue.SLASH SLASH1, _, _)) :: ( _, ( MlyValue.lident 
lident1, lident1left, _)) :: rest671)) => let val  result = 
MlyValue.fun_spec (fn _ => let val  (lident as lident1) = lident1 ()
 val  SLASH1 = SLASH1 ()
 val  (arity as arity1) = arity1 ()
 val  COLON1 = COLON1 ()
 val  (typ as typ1) = typ1 ()
 in ((lident, arity, SOME(typ)))
end)
 in ( LrTable.NT 18, ( result, lident1left, typ1right), rest671)
end
|  ( 33, ( ( _, ( MlyValue.rule rule1, rule1left, rule1right)) :: 
rest671)) => let val  result = MlyValue.analysis_spec (fn _ => let
 val  (rule as rule1) = rule1 ()
 in ([rule])
end)
 in ( LrTable.NT 21, ( result, rule1left, rule1right), rest671)
end
|  ( 34, ( ( _, ( MlyValue.analysis_spec analysis_spec1, _, 
analysis_spec1right)) :: ( _, ( MlyValue.rule rule1, rule1left, _)) ::
 rest671)) => let val  result = MlyValue.analysis_spec (fn _ => let
 val  (rule as rule1) = rule1 ()
 val  (analysis_spec as analysis_spec1) = analysis_spec1 ()
 in (rule::analysis_spec)
end)
 in ( LrTable.NT 21, ( result, rule1left, analysis_spec1right), 
rest671)
end
|  ( 35, ( ( _, ( MlyValue.result result1, _, result1right)) :: ( _, (
 MlyValue.ARROW ARROW1, _, _)) :: ( _, ( MlyValue.head head1, 
head1left, _)) :: rest671)) => let val  result = MlyValue.rule (fn _
 => let val  (head as head1) = head1 ()
 val  ARROW1 = ARROW1 ()
 val  (result as result1) = result1 ()
 in ((head,[],result))
end)
 in ( LrTable.NT 24, ( result, head1left, result1right), rest671)
end
|  ( 36, ( ( _, ( MlyValue.result result1, _, result1right)) :: ( _, (
 MlyValue.ARROW ARROW1, _, _)) :: ( _, ( MlyValue.keys keys1, _, _))
 :: ( _, ( MlyValue.QUESTION QUESTION1, _, _)) :: ( _, ( MlyValue.head
 head1, head1left, _)) :: rest671)) => let val  result = MlyValue.rule
 (fn _ => let val  (head as head1) = head1 ()
 val  QUESTION1 = QUESTION1 ()
 val  (keys as keys1) = keys1 ()
 val  ARROW1 = ARROW1 ()
 val  (result as result1) = result1 ()
 in ((head,keys,result))
end)
 in ( LrTable.NT 24, ( result, head1left, result1right), rest671)
end
|  ( 37, ( ( _, ( MlyValue.CLOSEP CLOSEP1, _, CLOSEP1right)) :: ( _, (
 MlyValue.head_params head_params1, _, _)) :: ( _, ( MlyValue.OPENP 
OPENP1, _, _)) :: ( _, ( MlyValue.LOWER_STRING_LITERAL 
LOWER_STRING_LITERAL1, LOWER_STRING_LITERAL1left, _)) :: rest671)) =>
 let val  result = MlyValue.head (fn _ => let val  (
LOWER_STRING_LITERAL as LOWER_STRING_LITERAL1) = LOWER_STRING_LITERAL1
 ()
 val  OPENP1 = OPENP1 ()
 val  (head_params as head_params1) = head_params1 ()
 val  CLOSEP1 = CLOSEP1 ()
 in ((LOWER_STRING_LITERAL,head_params))
end)
 in ( LrTable.NT 25, ( result, LOWER_STRING_LITERAL1left, CLOSEP1right
), rest671)
end
|  ( 38, ( ( _, ( MlyValue.UPPER_STRING_LITERAL UPPER_STRING_LITERAL1,
 UPPER_STRING_LITERAL1left, UPPER_STRING_LITERAL1right)) :: rest671))
 => let val  result = MlyValue.head_params (fn _ => let val  (
UPPER_STRING_LITERAL as UPPER_STRING_LITERAL1) = UPPER_STRING_LITERAL1
 ()
 in ([UPPER_STRING_LITERAL])
end)
 in ( LrTable.NT 26, ( result, UPPER_STRING_LITERAL1left, 
UPPER_STRING_LITERAL1right), rest671)
end
|  ( 39, ( ( _, ( MlyValue.head_params head_params1, _, 
head_params1right)) :: ( _, ( MlyValue.COMMA COMMA1, _, _)) :: ( _, ( 
MlyValue.UPPER_STRING_LITERAL UPPER_STRING_LITERAL1, 
UPPER_STRING_LITERAL1left, _)) :: rest671)) => let val  result = 
MlyValue.head_params (fn _ => let val  (UPPER_STRING_LITERAL as 
UPPER_STRING_LITERAL1) = UPPER_STRING_LITERAL1 ()
 val  COMMA1 = COMMA1 ()
 val  (head_params as head_params1) = head_params1 ()
 in ([UPPER_STRING_LITERAL]@head_params)
end)
 in ( LrTable.NT 26, ( result, UPPER_STRING_LITERAL1left, 
head_params1right), rest671)
end
|  ( 40, ( ( _, ( MlyValue.msgs msgs1, msgs1left, msgs1right)) :: 
rest671)) => let val  result = MlyValue.keys (fn _ => let val  (msgs
 as msgs1) = msgs1 ()
 in (msgs)
end)
 in ( LrTable.NT 27, ( result, msgs1left, msgs1right), rest671)
end
|  ( 41, ( ( _, ( MlyValue.UPPER_STRING_LITERAL UPPER_STRING_LITERAL1,
 UPPER_STRING_LITERAL1left, UPPER_STRING_LITERAL1right)) :: rest671))
 => let val  result = MlyValue.result (fn _ => let val  (
UPPER_STRING_LITERAL as UPPER_STRING_LITERAL1) = UPPER_STRING_LITERAL1
 ()
 in ([UPPER_STRING_LITERAL])
end)
 in ( LrTable.NT 28, ( result, UPPER_STRING_LITERAL1left, 
UPPER_STRING_LITERAL1right), rest671)
end
|  ( 42, ( ( _, ( MlyValue.result result1, _, result1right)) :: ( _, (
 MlyValue.COMMA COMMA1, _, _)) :: ( _, ( MlyValue.UPPER_STRING_LITERAL
 UPPER_STRING_LITERAL1, UPPER_STRING_LITERAL1left, _)) :: rest671)) =>
 let val  result = MlyValue.result (fn _ => let val  (
UPPER_STRING_LITERAL as UPPER_STRING_LITERAL1) = UPPER_STRING_LITERAL1
 ()
 val  COMMA1 = COMMA1 ()
 val  (result as result1) = result1 ()
 in ([UPPER_STRING_LITERAL]@result)
end)
 in ( LrTable.NT 28, ( result, UPPER_STRING_LITERAL1left, result1right
), rest671)
end
|  ( 43, ( ( _, ( MlyValue.TRANSACTIONS TRANSACTIONS1, 
TRANSACTIONS1left, TRANSACTIONS1right)) :: rest671)) => let val  
result = MlyValue.transaction_spec_head (fn _ => let val  
TRANSACTIONS1 = TRANSACTIONS1 ()
 in (NONE)
end)
 in ( LrTable.NT 22, ( result, TRANSACTIONS1left, TRANSACTIONS1right),
 rest671)
end
|  ( 44, ( ( _, ( MlyValue.LOWER_STRING_LITERAL LOWER_STRING_LITERAL1,
 _, LOWER_STRING_LITERAL1right)) :: ( _, ( MlyValue.OF OF1, _, _)) :: 
( _, ( MlyValue.TRANSACTIONS TRANSACTIONS1, TRANSACTIONS1left, _)) :: 
rest671)) => let val  result = MlyValue.transaction_spec_head (fn _ =>
 let val  TRANSACTIONS1 = TRANSACTIONS1 ()
 val  OF1 = OF1 ()
 val  (LOWER_STRING_LITERAL as LOWER_STRING_LITERAL1) = 
LOWER_STRING_LITERAL1 ()
 in (SOME LOWER_STRING_LITERAL)
end)
 in ( LrTable.NT 22, ( result, TRANSACTIONS1left, 
LOWER_STRING_LITERAL1right), rest671)
end
|  ( 45, ( ( _, ( MlyValue.DOT DOT1, _, DOT1right)) :: ( _, ( 
MlyValue.actions_ext actions_ext1, _, _)) :: ( _, ( 
MlyValue.transaction_name transaction_name1, transaction_name1left, _)
) :: rest671)) => let val  result = MlyValue.transaction_spec (fn _ =>
 let val  (transaction_name as transaction_name1) = transaction_name1
 ()
 val  (actions_ext as actions_ext1) = actions_ext1 ()
 val  DOT1 = DOT1 ()
 in ([TracProtocol.mkTransaction transaction_name actions_ext])
end)
 in ( LrTable.NT 23, ( result, transaction_name1left, DOT1right), 
rest671)
end
|  ( 46, ( ( _, ( MlyValue.transaction_spec transaction_spec1, _, 
transaction_spec1right)) :: ( _, ( MlyValue.DOT DOT1, _, _)) :: ( _, (
 MlyValue.actions_ext actions_ext1, _, _)) :: ( _, ( 
MlyValue.transaction_name transaction_name1, transaction_name1left, _)
) :: rest671)) => let val  result = MlyValue.transaction_spec (fn _ =>
 let val  (transaction_name as transaction_name1) = transaction_name1
 ()
 val  (actions_ext as actions_ext1) = actions_ext1 ()
 val  DOT1 = DOT1 ()
 val  (transaction_spec as transaction_spec1) = transaction_spec1 ()
 in (
(TracProtocol.mkTransaction transaction_name actions_ext)::transaction_spec
)
end)
 in ( LrTable.NT 23, ( result, transaction_name1left, 
transaction_spec1right), rest671)
end
|  ( 47, ( ( _, ( MlyValue.UPPER_STRING_LITERAL UPPER_STRING_LITERAL1,
 _, UPPER_STRING_LITERAL1right)) :: ( _, ( MlyValue.UNEQUAL UNEQUAL1, 
UNEQUAL1left, _)) :: rest671)) => let val  result = MlyValue.ineq_aux
 (fn _ => let val  UNEQUAL1 = UNEQUAL1 ()
 val  (UPPER_STRING_LITERAL as UPPER_STRING_LITERAL1) = 
UPPER_STRING_LITERAL1 ()
 in (UPPER_STRING_LITERAL)
end)
 in ( LrTable.NT 37, ( result, UNEQUAL1left, 
UPPER_STRING_LITERAL1right), rest671)
end
|  ( 48, ( ( _, ( MlyValue.ineq_aux ineq_aux1, _, ineq_aux1right)) :: 
( _, ( MlyValue.UPPER_STRING_LITERAL UPPER_STRING_LITERAL1, 
UPPER_STRING_LITERAL1left, _)) :: rest671)) => let val  result = 
MlyValue.ineq (fn _ => let val  (UPPER_STRING_LITERAL as 
UPPER_STRING_LITERAL1) = UPPER_STRING_LITERAL1 ()
 val  (ineq_aux as ineq_aux1) = ineq_aux1 ()
 in ((UPPER_STRING_LITERAL,ineq_aux))
end)
 in ( LrTable.NT 38, ( result, UPPER_STRING_LITERAL1left, 
ineq_aux1right), rest671)
end
|  ( 49, ( ( _, ( MlyValue.ineq ineq1, ineq1left, ineq1right)) :: 
rest671)) => let val  result = MlyValue.ineqs (fn _ => let val  (ineq
 as ineq1) = ineq1 ()
 in ([ineq])
end)
 in ( LrTable.NT 39, ( result, ineq1left, ineq1right), rest671)
end
|  ( 50, ( ( _, ( MlyValue.ineqs ineqs1, _, ineqs1right)) :: ( _, ( 
MlyValue.COMMA COMMA1, _, _)) :: ( _, ( MlyValue.ineq ineq1, ineq1left
, _)) :: rest671)) => let val  result = MlyValue.ineqs (fn _ => let
 val  (ineq as ineq1) = ineq1 ()
 val  COMMA1 = COMMA1 ()
 val  (ineqs as ineqs1) = ineqs1 ()
 in ([ineq]@ineqs)
end)
 in ( LrTable.NT 39, ( result, ineq1left, ineqs1right), rest671)
end
|  ( 51, ( ( _, ( MlyValue.ineqs ineqs1, _, ineqs1right)) :: ( _, ( 
MlyValue.WHERE WHERE1, _, _)) :: ( _, ( MlyValue.CLOSEP CLOSEP1, _, _)
) :: ( _, ( MlyValue.vars_typs vars_typs1, _, _)) :: ( _, ( 
MlyValue.OPENP OPENP1, _, _)) :: ( _, ( MlyValue.ident ident1, 
ident1left, _)) :: rest671)) => let val  result = 
MlyValue.transaction_name (fn _ => let val  (ident as ident1) = ident1
 ()
 val  OPENP1 = OPENP1 ()
 val  (vars_typs as vars_typs1) = vars_typs1 ()
 val  CLOSEP1 = CLOSEP1 ()
 val  WHERE1 = WHERE1 ()
 val  (ineqs as ineqs1) = ineqs1 ()
 in ((ident,vars_typs,ineqs))
end)
 in ( LrTable.NT 40, ( result, ident1left, ineqs1right), rest671)
end
|  ( 52, ( ( _, ( MlyValue.CLOSEP CLOSEP1, _, CLOSEP1right)) :: ( _, (
 MlyValue.vars_typs vars_typs1, _, _)) :: ( _, ( MlyValue.OPENP OPENP1
, _, _)) :: ( _, ( MlyValue.ident ident1, ident1left, _)) :: rest671))
 => let val  result = MlyValue.transaction_name (fn _ => let val  (
ident as ident1) = ident1 ()
 val  OPENP1 = OPENP1 ()
 val  (vars_typs as vars_typs1) = vars_typs1 ()
 val  CLOSEP1 = CLOSEP1 ()
 in ((ident,vars_typs,[]))
end)
 in ( LrTable.NT 40, ( result, ident1left, CLOSEP1right), rest671)
end
|  ( 53, ( ( _, ( MlyValue.CLOSEP CLOSEP1, _, CLOSEP1right)) :: ( _, (
 MlyValue.OPENP OPENP1, _, _)) :: ( _, ( MlyValue.ident ident1, 
ident1left, _)) :: rest671)) => let val  result = 
MlyValue.transaction_name (fn _ => let val  (ident as ident1) = ident1
 ()
 val  OPENP1 = OPENP1 ()
 val  CLOSEP1 = CLOSEP1 ()
 in ((ident,[],[]))
end)
 in ( LrTable.NT 40, ( result, ident1left, CLOSEP1right), rest671)
end
|  ( 54, ( ( _, ( MlyValue.CLOSESQB CLOSESQB1, _, CLOSESQB1right)) :: 
( _, ( MlyValue.OPENSQB OPENSQB1, _, _)) :: ( _, ( MlyValue.EXCLAM 
EXCLAM1, _, _)) :: ( _, ( MlyValue.ident ident1, ident1left, _)) :: 
rest671)) => let val  result = MlyValue.abbrev (fn _ => let val  (
ident as ident1) = ident1 ()
 val  EXCLAM1 = EXCLAM1 ()
 val  OPENSQB1 = OPENSQB1 ()
 val  CLOSESQB1 = CLOSESQB1 ()
 in ((ident,[]))
end)
 in ( LrTable.NT 49, ( result, ident1left, CLOSESQB1right), rest671)

end
|  ( 55, ( ( _, ( MlyValue.CLOSESQB CLOSESQB1, _, CLOSESQB1right)) :: 
( _, ( MlyValue.msgs msgs1, _, _)) :: ( _, ( MlyValue.OPENSQB OPENSQB1
, _, _)) :: ( _, ( MlyValue.EXCLAM EXCLAM1, _, _)) :: ( _, ( 
MlyValue.ident ident1, ident1left, _)) :: rest671)) => let val  result
 = MlyValue.abbrev (fn _ => let val  (ident as ident1) = ident1 ()
 val  EXCLAM1 = EXCLAM1 ()
 val  OPENSQB1 = OPENSQB1 ()
 val  (msgs as msgs1) = msgs1 ()
 val  CLOSESQB1 = CLOSESQB1 ()
 in ((ident,msgs))
end)
 in ( LrTable.NT 49, ( result, ident1left, CLOSESQB1right), rest671)

end
|  ( 56, ( ( _, ( MlyValue.action action1, action1left, action1right))
 :: rest671)) => let val  result = MlyValue.actions (fn _ => let val 
 (action as action1) = action1 ()
 in ([action])
end)
 in ( LrTable.NT 34, ( result, action1left, action1right), rest671)

end
|  ( 57, ( ( _, ( MlyValue.actions actions1, _, actions1right)) :: ( _
, ( MlyValue.action action1, action1left, _)) :: rest671)) => let val 
 result = MlyValue.actions (fn _ => let val  (action as action1) = 
action1 ()
 val  (actions as actions1) = actions1 ()
 in (action::actions)
end)
 in ( LrTable.NT 34, ( result, action1left, actions1right), rest671)

end
|  ( 58, ( ( _, ( MlyValue.msgs msgs1, _, msgs1right)) :: ( _, ( 
MlyValue.RECEIVE RECEIVE1, RECEIVE1left, _)) :: rest671)) => let val  
result = MlyValue.action (fn _ => let val  (RECEIVE as RECEIVE1) = 
RECEIVE1 ()
 val  (msgs as msgs1) = msgs1 ()
 in ((TracProtocol.LabelN,TracProtocol.RECEIVE(msgs)))
end)
 in ( LrTable.NT 33, ( result, RECEIVE1left, msgs1right), rest671)
end
|  ( 59, ( ( _, ( MlyValue.msgs msgs1, _, msgs1right)) :: ( _, ( 
MlyValue.SEND SEND1, SEND1left, _)) :: rest671)) => let val  result = 
MlyValue.action (fn _ => let val  (SEND as SEND1) = SEND1 ()
 val  (msgs as msgs1) = msgs1 ()
 in ((TracProtocol.LabelN,TracProtocol.SEND(msgs)))
end)
 in ( LrTable.NT 33, ( result, SEND1left, msgs1right), rest671)
end
|  ( 60, ( ( _, ( MlyValue.msg msg2, _, msg2right)) :: ( _, ( 
MlyValue.DOUBLEEQUAL DOUBLEEQUAL1, _, _)) :: ( _, ( MlyValue.msg msg1,
 msg1left, _)) :: rest671)) => let val  result = MlyValue.action (fn _
 => let val  msg1 = msg1 ()
 val  DOUBLEEQUAL1 = DOUBLEEQUAL1 ()
 val  msg2 = msg2 ()
 in ((TracProtocol.LabelN,TracProtocol.EQUATION(msg1,msg2)))
end)
 in ( LrTable.NT 33, ( result, msg1left, msg2right), rest671)
end
|  ( 61, ( ( _, ( MlyValue.msg msg2, _, msg2right)) :: ( _, ( 
MlyValue.EQUAL EQUAL1, _, _)) :: ( _, ( MlyValue.msg msg1, _, _)) :: (
 _, ( MlyValue.LET LET1, LET1left, _)) :: rest671)) => let val  result
 = MlyValue.action (fn _ => let val  LET1 = LET1 ()
 val  msg1 = msg1 ()
 val  EQUAL1 = EQUAL1 ()
 val  msg2 = msg2 ()
 in ((TracProtocol.LabelN,TracProtocol.LETBINDING(msg1,msg2)))
end)
 in ( LrTable.NT 33, ( result, LET1left, msg2right), rest671)
end
|  ( 62, ( ( _, ( MlyValue.setexp setexp1, _, setexp1right)) :: ( _, (
 MlyValue.IN IN1, _, _)) :: ( _, ( MlyValue.msg msg1, msg1left, _)) ::
 rest671)) => let val  result = MlyValue.action (fn _ => let val  (msg
 as msg1) = msg1 ()
 val  (IN as IN1) = IN1 ()
 val  (setexp as setexp1) = setexp1 ()
 in ((TracProtocol.LabelN,TracProtocol.IN(msg,setexp)))
end)
 in ( LrTable.NT 33, ( result, msg1left, setexp1right), rest671)
end
|  ( 63, ( ( _, ( MlyValue.CLOSEP CLOSEP1, _, CLOSEP1right)) :: ( _, (
 MlyValue.UNDERSCORE UNDERSCORE1, _, _)) :: ( _, ( MlyValue.OPENP 
OPENP1, _, _)) :: ( _, ( MlyValue.lident lident1, _, _)) :: ( _, ( 
MlyValue.NOTIN NOTIN1, _, _)) :: ( _, ( MlyValue.msg msg1, msg1left, _
)) :: rest671)) => let val  result = MlyValue.action (fn _ => let val 
 (msg as msg1) = msg1 ()
 val  NOTIN1 = NOTIN1 ()
 val  (lident as lident1) = lident1 ()
 val  OPENP1 = OPENP1 ()
 val  UNDERSCORE1 = UNDERSCORE1 ()
 val  CLOSEP1 = CLOSEP1 ()
 in ((TracProtocol.LabelN,TracProtocol.NOTINANY(msg,lident)))
end)
 in ( LrTable.NT 33, ( result, msg1left, CLOSEP1right), rest671)
end
|  ( 64, ( ( _, ( MlyValue.negcheck_disj negcheck_disj1, 
negcheck_disj1left, negcheck_disj1right)) :: rest671)) => let val  
result = MlyValue.action (fn _ => let val  (negcheck_disj as 
negcheck_disj1) = negcheck_disj1 ()
 in ((TracProtocol.LabelN,TracProtocol.NEGCHECKS([],negcheck_disj)))

end)
 in ( LrTable.NT 33, ( result, negcheck_disj1left, negcheck_disj1right
), rest671)
end
|  ( 65, ( ( _, ( MlyValue.vars_typs vars_typs1, _, vars_typs1right))
 :: ( _, ( MlyValue.FORALL FORALL1, _, _)) :: ( _, ( 
MlyValue.negcheck_disj negcheck_disj1, negcheck_disj1left, _)) :: 
rest671)) => let val  result = MlyValue.action (fn _ => let val  (
negcheck_disj as negcheck_disj1) = negcheck_disj1 ()
 val  FORALL1 = FORALL1 ()
 val  (vars_typs as vars_typs1) = vars_typs1 ()
 in (
(TracProtocol.LabelN,TracProtocol.NEGCHECKS(vars_typs,negcheck_disj)))

end)
 in ( LrTable.NT 33, ( result, negcheck_disj1left, vars_typs1right), 
rest671)
end
|  ( 66, ( ( _, ( MlyValue.setexp setexp1, _, setexp1right)) :: ( _, (
 MlyValue.msg msg1, _, _)) :: ( _, ( MlyValue.INSERT INSERT1, 
INSERT1left, _)) :: rest671)) => let val  result = MlyValue.action (fn
 _ => let val  (INSERT as INSERT1) = INSERT1 ()
 val  (msg as msg1) = msg1 ()
 val  (setexp as setexp1) = setexp1 ()
 in ((TracProtocol.LabelN,TracProtocol.INSERT(msg,setexp)))
end)
 in ( LrTable.NT 33, ( result, INSERT1left, setexp1right), rest671)

end
|  ( 67, ( ( _, ( MlyValue.setexp setexp1, _, setexp1right)) :: ( _, (
 MlyValue.msg msg1, _, _)) :: ( _, ( MlyValue.DELETE DELETE1, 
DELETE1left, _)) :: rest671)) => let val  result = MlyValue.action (fn
 _ => let val  (DELETE as DELETE1) = DELETE1 ()
 val  (msg as msg1) = msg1 ()
 val  (setexp as setexp1) = setexp1 ()
 in ((TracProtocol.LabelN,TracProtocol.DELETE(msg,setexp)))
end)
 in ( LrTable.NT 33, ( result, DELETE1left, setexp1right), rest671)

end
|  ( 68, ( ( _, ( MlyValue.vars_opts vars_opts1, _, vars_opts1right))
 :: ( _, ( MlyValue.NEW NEW1, NEW1left, _)) :: rest671)) => let val  
result = MlyValue.action (fn _ => let val  (NEW as NEW1) = NEW1 ()
 val  (vars_opts as vars_opts1) = vars_opts1 ()
 in ((TracProtocol.LabelS,TracProtocol.NEW(vars_opts)))
end)
 in ( LrTable.NT 33, ( result, NEW1left, vars_opts1right), rest671)

end
|  ( 69, ( ( _, ( MlyValue.ATTACK ATTACK1, ATTACK1left, ATTACK1right))
 :: rest671)) => let val  result = MlyValue.action (fn _ => let val  (
ATTACK as ATTACK1) = ATTACK1 ()
 in ((TracProtocol.LabelN,TracProtocol.ATTACK))
end)
 in ( LrTable.NT 33, ( result, ATTACK1left, ATTACK1right), rest671)

end
|  ( 70, ( ( _, ( MlyValue.msgs msgs1, _, msgs1right)) :: ( _, ( 
MlyValue.RECEIVE RECEIVE1, _, _)) :: ( _, ( MlyValue.STAR STAR1, 
STAR1left, _)) :: rest671)) => let val  result = MlyValue.action (fn _
 => let val  STAR1 = STAR1 ()
 val  (RECEIVE as RECEIVE1) = RECEIVE1 ()
 val  (msgs as msgs1) = msgs1 ()
 in ((TracProtocol.LabelS,TracProtocol.RECEIVE(msgs)))
end)
 in ( LrTable.NT 33, ( result, STAR1left, msgs1right), rest671)
end
|  ( 71, ( ( _, ( MlyValue.msgs msgs1, _, msgs1right)) :: ( _, ( 
MlyValue.SEND SEND1, _, _)) :: ( _, ( MlyValue.STAR STAR1, STAR1left,
 _)) :: rest671)) => let val  result = MlyValue.action (fn _ => let
 val  STAR1 = STAR1 ()
 val  (SEND as SEND1) = SEND1 ()
 val  (msgs as msgs1) = msgs1 ()
 in ((TracProtocol.LabelS,TracProtocol.SEND(msgs)))
end)
 in ( LrTable.NT 33, ( result, STAR1left, msgs1right), rest671)
end
|  ( 72, ( ( _, ( MlyValue.msg msg2, _, msg2right)) :: ( _, ( 
MlyValue.DOUBLEEQUAL DOUBLEEQUAL1, _, _)) :: ( _, ( MlyValue.msg msg1,
 _, _)) :: ( _, ( MlyValue.STAR STAR1, STAR1left, _)) :: rest671)) =>
 let val  result = MlyValue.action (fn _ => let val  STAR1 = STAR1 ()
 val  msg1 = msg1 ()
 val  DOUBLEEQUAL1 = DOUBLEEQUAL1 ()
 val  msg2 = msg2 ()
 in ((TracProtocol.LabelS,TracProtocol.EQUATION(msg1,msg2)))
end)
 in ( LrTable.NT 33, ( result, STAR1left, msg2right), rest671)
end
|  ( 73, ( ( _, ( MlyValue.msg msg2, _, msg2right)) :: ( _, ( 
MlyValue.EQUAL EQUAL1, _, _)) :: ( _, ( MlyValue.msg msg1, _, _)) :: (
 _, ( MlyValue.LET LET1, _, _)) :: ( _, ( MlyValue.STAR STAR1, 
STAR1left, _)) :: rest671)) => let val  result = MlyValue.action (fn _
 => let val  STAR1 = STAR1 ()
 val  LET1 = LET1 ()
 val  msg1 = msg1 ()
 val  EQUAL1 = EQUAL1 ()
 val  msg2 = msg2 ()
 in ((TracProtocol.LabelS,TracProtocol.LETBINDING(msg1,msg2)))
end)
 in ( LrTable.NT 33, ( result, STAR1left, msg2right), rest671)
end
|  ( 74, ( ( _, ( MlyValue.setexp setexp1, _, setexp1right)) :: ( _, (
 MlyValue.IN IN1, _, _)) :: ( _, ( MlyValue.msg msg1, _, _)) :: ( _, (
 MlyValue.STAR STAR1, STAR1left, _)) :: rest671)) => let val  result =
 MlyValue.action (fn _ => let val  STAR1 = STAR1 ()
 val  (msg as msg1) = msg1 ()
 val  (IN as IN1) = IN1 ()
 val  (setexp as setexp1) = setexp1 ()
 in ((TracProtocol.LabelS,TracProtocol.IN(msg,setexp)))
end)
 in ( LrTable.NT 33, ( result, STAR1left, setexp1right), rest671)
end
|  ( 75, ( ( _, ( MlyValue.CLOSEP CLOSEP1, _, CLOSEP1right)) :: ( _, (
 MlyValue.UNDERSCORE UNDERSCORE1, _, _)) :: ( _, ( MlyValue.OPENP 
OPENP1, _, _)) :: ( _, ( MlyValue.lident lident1, _, _)) :: ( _, ( 
MlyValue.NOTIN NOTIN1, _, _)) :: ( _, ( MlyValue.msg msg1, _, _)) :: (
 _, ( MlyValue.STAR STAR1, STAR1left, _)) :: rest671)) => let val  
result = MlyValue.action (fn _ => let val  STAR1 = STAR1 ()
 val  (msg as msg1) = msg1 ()
 val  NOTIN1 = NOTIN1 ()
 val  (lident as lident1) = lident1 ()
 val  OPENP1 = OPENP1 ()
 val  UNDERSCORE1 = UNDERSCORE1 ()
 val  CLOSEP1 = CLOSEP1 ()
 in ((TracProtocol.LabelS,TracProtocol.NOTINANY(msg,lident)))
end)
 in ( LrTable.NT 33, ( result, STAR1left, CLOSEP1right), rest671)
end
|  ( 76, ( ( _, ( MlyValue.negcheck_disj negcheck_disj1, _, 
negcheck_disj1right)) :: ( _, ( MlyValue.STAR STAR1, STAR1left, _)) ::
 rest671)) => let val  result = MlyValue.action (fn _ => let val  
STAR1 = STAR1 ()
 val  (negcheck_disj as negcheck_disj1) = negcheck_disj1 ()
 in ((TracProtocol.LabelS,TracProtocol.NEGCHECKS([],negcheck_disj)))

end)
 in ( LrTable.NT 33, ( result, STAR1left, negcheck_disj1right), 
rest671)
end
|  ( 77, ( ( _, ( MlyValue.vars_typs vars_typs1, _, vars_typs1right))
 :: ( _, ( MlyValue.FORALL FORALL1, _, _)) :: ( _, ( 
MlyValue.negcheck_disj negcheck_disj1, _, _)) :: ( _, ( MlyValue.STAR 
STAR1, STAR1left, _)) :: rest671)) => let val  result = 
MlyValue.action (fn _ => let val  STAR1 = STAR1 ()
 val  (negcheck_disj as negcheck_disj1) = negcheck_disj1 ()
 val  FORALL1 = FORALL1 ()
 val  (vars_typs as vars_typs1) = vars_typs1 ()
 in (
(TracProtocol.LabelS,TracProtocol.NEGCHECKS(vars_typs,negcheck_disj)))

end)
 in ( LrTable.NT 33, ( result, STAR1left, vars_typs1right), rest671)

end
|  ( 78, ( ( _, ( MlyValue.setexp setexp1, _, setexp1right)) :: ( _, (
 MlyValue.msg msg1, _, _)) :: ( _, ( MlyValue.INSERT INSERT1, _, _))
 :: ( _, ( MlyValue.STAR STAR1, STAR1left, _)) :: rest671)) => let
 val  result = MlyValue.action (fn _ => let val  STAR1 = STAR1 ()
 val  (INSERT as INSERT1) = INSERT1 ()
 val  (msg as msg1) = msg1 ()
 val  (setexp as setexp1) = setexp1 ()
 in ((TracProtocol.LabelS,TracProtocol.INSERT(msg,setexp)))
end)
 in ( LrTable.NT 33, ( result, STAR1left, setexp1right), rest671)
end
|  ( 79, ( ( _, ( MlyValue.setexp setexp1, _, setexp1right)) :: ( _, (
 MlyValue.msg msg1, _, _)) :: ( _, ( MlyValue.DELETE DELETE1, _, _))
 :: ( _, ( MlyValue.STAR STAR1, STAR1left, _)) :: rest671)) => let
 val  result = MlyValue.action (fn _ => let val  STAR1 = STAR1 ()
 val  (DELETE as DELETE1) = DELETE1 ()
 val  (msg as msg1) = msg1 ()
 val  (setexp as setexp1) = setexp1 ()
 in ((TracProtocol.LabelS,TracProtocol.DELETE(msg,setexp)))
end)
 in ( LrTable.NT 33, ( result, STAR1left, setexp1right), rest671)
end
|  ( 80, ( ( _, ( MlyValue.abbrev abbrev1, abbrev1left, abbrev1right))
 :: rest671)) => let val  result = MlyValue.action_ext (fn _ => let
 val  (abbrev as abbrev1) = abbrev1 ()
 in (TracProtocol.ABBREVIATION(abbrev))
end)
 in ( LrTable.NT 35, ( result, abbrev1left, abbrev1right), rest671)

end
|  ( 81, ( ( _, ( MlyValue.action action1, action1left, action1right))
 :: rest671)) => let val  result = MlyValue.action_ext (fn _ => let
 val  (action as action1) = action1 ()
 in (TracProtocol.LABELED_ACTION(action))
end)
 in ( LrTable.NT 35, ( result, action1left, action1right), rest671)

end
|  ( 82, ( ( _, ( MlyValue.action_ext action_ext1, action_ext1left, 
action_ext1right)) :: rest671)) => let val  result = 
MlyValue.actions_ext (fn _ => let val  (action_ext as action_ext1) = 
action_ext1 ()
 in ([action_ext])
end)
 in ( LrTable.NT 36, ( result, action_ext1left, action_ext1right), 
rest671)
end
|  ( 83, ( ( _, ( MlyValue.actions_ext actions_ext1, _, 
actions_ext1right)) :: ( _, ( MlyValue.action_ext action_ext1, 
action_ext1left, _)) :: rest671)) => let val  result = 
MlyValue.actions_ext (fn _ => let val  (action_ext as action_ext1) = 
action_ext1 ()
 val  (actions_ext as actions_ext1) = actions_ext1 ()
 in (action_ext::actions_ext)
end)
 in ( LrTable.NT 36, ( result, action_ext1left, actions_ext1right), 
rest671)
end
|  ( 84, ( ( _, ( MlyValue.UPPER_STRING_LITERAL UPPER_STRING_LITERAL1,
 UPPER_STRING_LITERAL1left, UPPER_STRING_LITERAL1right)) :: rest671))
 => let val  result = MlyValue.typ (fn _ => let val  (
UPPER_STRING_LITERAL as UPPER_STRING_LITERAL1) = UPPER_STRING_LITERAL1
 ()
 in (Trac_Term.TAtom(UPPER_STRING_LITERAL))
end)
 in ( LrTable.NT 41, ( result, UPPER_STRING_LITERAL1left, 
UPPER_STRING_LITERAL1right), rest671)
end
|  ( 85, ( ( _, ( MlyValue.LOWER_STRING_LITERAL LOWER_STRING_LITERAL1,
 LOWER_STRING_LITERAL1left, LOWER_STRING_LITERAL1right)) :: rest671))
 => let val  result = MlyValue.typ (fn _ => let val  (
LOWER_STRING_LITERAL as LOWER_STRING_LITERAL1) = LOWER_STRING_LITERAL1
 ()
 in (Trac_Term.TAtom(LOWER_STRING_LITERAL))
end)
 in ( LrTable.NT 41, ( result, LOWER_STRING_LITERAL1left, 
LOWER_STRING_LITERAL1right), rest671)
end
|  ( 86, ( ( _, ( MlyValue.CLOSEP CLOSEP1, _, CLOSEP1right)) :: ( _, (
 MlyValue.typs typs1, _, _)) :: ( _, ( MlyValue.OPENP OPENP1, _, _))
 :: ( _, ( MlyValue.LOWER_STRING_LITERAL LOWER_STRING_LITERAL1, 
LOWER_STRING_LITERAL1left, _)) :: rest671)) => let val  result = 
MlyValue.typ (fn _ => let val  (LOWER_STRING_LITERAL as 
LOWER_STRING_LITERAL1) = LOWER_STRING_LITERAL1 ()
 val  OPENP1 = OPENP1 ()
 val  (typs as typs1) = typs1 ()
 val  CLOSEP1 = CLOSEP1 ()
 in (Trac_Term.TComp(LOWER_STRING_LITERAL,typs))
end)
 in ( LrTable.NT 41, ( result, LOWER_STRING_LITERAL1left, CLOSEP1right
), rest671)
end
|  ( 87, ( ( _, ( MlyValue.typ typ1, typ1left, typ1right)) :: rest671)
) => let val  result = MlyValue.typs (fn _ => let val  (typ as typ1) =
 typ1 ()
 in ([typ])
end)
 in ( LrTable.NT 42, ( result, typ1left, typ1right), rest671)
end
|  ( 88, ( ( _, ( MlyValue.typs typs1, _, typs1right)) :: ( _, ( 
MlyValue.COMMA COMMA1, _, _)) :: ( _, ( MlyValue.typ typ1, typ1left, _
)) :: rest671)) => let val  result = MlyValue.typs (fn _ => let val  (
typ as typ1) = typ1 ()
 val  COMMA1 = COMMA1 ()
 val  (typs as typs1) = typs1 ()
 in (typ::typs)
end)
 in ( LrTable.NT 42, ( result, typ1left, typs1right), rest671)
end
|  ( 89, ( ( _, ( MlyValue.uident uident1, uident1left, uident1right))
 :: rest671)) => let val  result = MlyValue.vars (fn _ => let val  (
uident as uident1) = uident1 ()
 in ([uident])
end)
 in ( LrTable.NT 43, ( result, uident1left, uident1right), rest671)

end
|  ( 90, ( ( _, ( MlyValue.vars vars1, _, vars1right)) :: ( _, ( 
MlyValue.COMMA COMMA1, _, _)) :: ( _, ( MlyValue.uident uident1, 
uident1left, _)) :: rest671)) => let val  result = MlyValue.vars (fn _
 => let val  (uident as uident1) = uident1 ()
 val  COMMA1 = COMMA1 ()
 val  (vars as vars1) = vars1 ()
 in (uident::vars)
end)
 in ( LrTable.NT 43, ( result, uident1left, vars1right), rest671)
end
|  ( 91, ( ( _, ( MlyValue.typ typ1, _, typ1right)) :: ( _, ( 
MlyValue.COLON COLON1, _, _)) :: ( _, ( MlyValue.vars vars1, vars1left
, _)) :: rest671)) => let val  result = MlyValue.vars_typ (fn _ => let
 val  (vars as vars1) = vars1 ()
 val  COLON1 = COLON1 ()
 val  (typ as typ1) = typ1 ()
 in ((vars,typ))
end)
 in ( LrTable.NT 44, ( result, vars1left, typ1right), rest671)
end
|  ( 92, ( ( _, ( MlyValue.vars_typ vars_typ1, vars_typ1left, 
vars_typ1right)) :: rest671)) => let val  result = MlyValue.vars_typs
 (fn _ => let val  (vars_typ as vars_typ1) = vars_typ1 ()
 in ([vars_typ])
end)
 in ( LrTable.NT 45, ( result, vars_typ1left, vars_typ1right), rest671
)
end
|  ( 93, ( ( _, ( MlyValue.vars_typs vars_typs1, _, vars_typs1right))
 :: ( _, ( MlyValue.COMMA COMMA1, _, _)) :: ( _, ( MlyValue.vars_typ 
vars_typ1, vars_typ1left, _)) :: rest671)) => let val  result = 
MlyValue.vars_typs (fn _ => let val  (vars_typ as vars_typ1) = 
vars_typ1 ()
 val  COMMA1 = COMMA1 ()
 val  (vars_typs as vars_typs1) = vars_typs1 ()
 in (vars_typ::vars_typs)
end)
 in ( LrTable.NT 45, ( result, vars_typ1left, vars_typs1right), 
rest671)
end
|  ( 94, ( ( _, ( MlyValue.vars vars1, vars1left, vars1right)) :: 
rest671)) => let val  result = MlyValue.vars_opts (fn _ => let val  (
vars as vars1) = vars1 ()
 in ([(vars,Trac_Term.TAtom(Trac_Utils.value_trac_typeN))])
end)
 in ( LrTable.NT 46, ( result, vars1left, vars1right), rest671)
end
|  ( 95, ( ( _, ( MlyValue.vars_typs vars_typs1, vars_typs1left, 
vars_typs1right)) :: rest671)) => let val  result = MlyValue.vars_opts
 (fn _ => let val  (vars_typs as vars_typs1) = vars_typs1 ()
 in (vars_typs)
end)
 in ( LrTable.NT 46, ( result, vars_typs1left, vars_typs1right), 
rest671)
end
|  ( 96, ( ( _, ( MlyValue.lident lident1, lident1left, lident1right))
 :: rest671)) => let val  result = MlyValue.setexp (fn _ => let val  (
lident as lident1) = lident1 ()
 in ((lident,[]))
end)
 in ( LrTable.NT 32, ( result, lident1left, lident1right), rest671)

end
|  ( 97, ( ( _, ( MlyValue.CLOSEP CLOSEP1, _, CLOSEP1right)) :: ( _, (
 MlyValue.msgs msgs1, _, _)) :: ( _, ( MlyValue.OPENP OPENP1, _, _))
 :: ( _, ( MlyValue.lident lident1, lident1left, _)) :: rest671)) =>
 let val  result = MlyValue.setexp (fn _ => let val  (lident as 
lident1) = lident1 ()
 val  OPENP1 = OPENP1 ()
 val  (msgs as msgs1) = msgs1 ()
 val  CLOSEP1 = CLOSEP1 ()
 in ((lident,msgs))
end)
 in ( LrTable.NT 32, ( result, lident1left, CLOSEP1right), rest671)

end
|  ( 98, ( ( _, ( MlyValue.negcheck negcheck1, negcheck1left, 
negcheck1right)) :: rest671)) => let val  result = 
MlyValue.negcheck_disj (fn _ => let val  (negcheck as negcheck1) = 
negcheck1 ()
 in ([negcheck])
end)
 in ( LrTable.NT 47, ( result, negcheck1left, negcheck1right), rest671
)
end
|  ( 99, ( ( _, ( MlyValue.negcheck_disj negcheck_disj1, _, 
negcheck_disj1right)) :: ( _, ( MlyValue.OR OR1, _, _)) :: ( _, ( 
MlyValue.negcheck negcheck1, negcheck1left, _)) :: rest671)) => let
 val  result = MlyValue.negcheck_disj (fn _ => let val  (negcheck as 
negcheck1) = negcheck1 ()
 val  OR1 = OR1 ()
 val  (negcheck_disj as negcheck_disj1) = negcheck_disj1 ()
 in (negcheck::negcheck_disj)
end)
 in ( LrTable.NT 47, ( result, negcheck1left, negcheck_disj1right), 
rest671)
end
|  ( 100, ( ( _, ( MlyValue.msg msg2, _, msg2right)) :: ( _, ( 
MlyValue.UNEQUAL UNEQUAL1, _, _)) :: ( _, ( MlyValue.msg msg1, 
msg1left, _)) :: rest671)) => let val  result = MlyValue.negcheck (fn
 _ => let val  msg1 = msg1 ()
 val  UNEQUAL1 = UNEQUAL1 ()
 val  msg2 = msg2 ()
 in (TracProtocol.INEQ(msg1,msg2))
end)
 in ( LrTable.NT 48, ( result, msg1left, msg2right), rest671)
end
|  ( 101, ( ( _, ( MlyValue.setexp setexp1, _, setexp1right)) :: ( _, 
( MlyValue.NOTIN NOTIN1, _, _)) :: ( _, ( MlyValue.msg msg1, msg1left,
 _)) :: rest671)) => let val  result = MlyValue.negcheck (fn _ => let
 val  (msg as msg1) = msg1 ()
 val  (NOTIN as NOTIN1) = NOTIN1 ()
 val  (setexp as setexp1) = setexp1 ()
 in (TracProtocol.NOTIN(msg,setexp))
end)
 in ( LrTable.NT 48, ( result, msg1left, setexp1right), rest671)
end
|  ( 102, ( ( _, ( MlyValue.uident uident1, uident1left, uident1right)
) :: rest671)) => let val  result = MlyValue.msg_atom (fn _ => let
 val  (uident as uident1) = uident1 ()
 in (Var(uident))
end)
 in ( LrTable.NT 29, ( result, uident1left, uident1right), rest671)

end
|  ( 103, ( ( _, ( MlyValue.lident lident1, lident1left, lident1right)
) :: rest671)) => let val  result = MlyValue.msg_atom (fn _ => let
 val  (lident as lident1) = lident1 ()
 in (Const(lident))
end)
 in ( LrTable.NT 29, ( result, lident1left, lident1right), rest671)

end
|  ( 104, ( ( _, ( MlyValue.msg_atom msg_atom1, msg_atom1left, 
msg_atom1right)) :: rest671)) => let val  result = MlyValue.msg (fn _
 => let val  (msg_atom as msg_atom1) = msg_atom1 ()
 in (msg_atom)
end)
 in ( LrTable.NT 30, ( result, msg_atom1left, msg_atom1right), rest671
)
end
|  ( 105, ( ( _, ( MlyValue.CLOSEP CLOSEP1, _, CLOSEP1right)) :: ( _, 
( MlyValue.msgs msgs1, _, _)) :: ( _, ( MlyValue.OPENP OPENP1, _, _))
 :: ( _, ( MlyValue.lident lident1, lident1left, _)) :: rest671)) =>
 let val  result = MlyValue.msg (fn _ => let val  (lident as lident1)
 = lident1 ()
 val  OPENP1 = OPENP1 ()
 val  (msgs as msgs1) = msgs1 ()
 val  CLOSEP1 = CLOSEP1 ()
 in (Fun(lident,msgs))
end)
 in ( LrTable.NT 30, ( result, lident1left, CLOSEP1right), rest671)

end
|  ( 106, ( ( _, ( MlyValue.abbrev abbrev1, abbrev1left, abbrev1right)
) :: rest671)) => let val  result = MlyValue.msg (fn _ => let val  (
abbrev as abbrev1) = abbrev1 ()
 in (Abbrev(abbrev))
end)
 in ( LrTable.NT 30, ( result, abbrev1left, abbrev1right), rest671)

end
|  ( 107, ( ( _, ( MlyValue.msg msg1, msg1left, msg1right)) :: rest671
)) => let val  result = MlyValue.msgs (fn _ => let val  (msg as msg1)
 = msg1 ()
 in ([msg])
end)
 in ( LrTable.NT 31, ( result, msg1left, msg1right), rest671)
end
|  ( 108, ( ( _, ( MlyValue.msgs msgs1, _, msgs1right)) :: ( _, ( 
MlyValue.COMMA COMMA1, _, _)) :: ( _, ( MlyValue.msg msg1, msg1left, _
)) :: rest671)) => let val  result = MlyValue.msgs (fn _ => let val  (
msg as msg1) = msg1 ()
 val  COMMA1 = COMMA1 ()
 val  (msgs as msgs1) = msgs1 ()
 in (msg::msgs)
end)
 in ( LrTable.NT 31, ( result, msg1left, msgs1right), rest671)
end
|  ( 109, ( ( _, ( MlyValue.UPPER_STRING_LITERAL UPPER_STRING_LITERAL1
, UPPER_STRING_LITERAL1left, UPPER_STRING_LITERAL1right)) :: rest671))
 => let val  result = MlyValue.name (fn _ => let val  (
UPPER_STRING_LITERAL as UPPER_STRING_LITERAL1) = UPPER_STRING_LITERAL1
 ()
 in (UPPER_STRING_LITERAL)
end)
 in ( LrTable.NT 1, ( result, UPPER_STRING_LITERAL1left, 
UPPER_STRING_LITERAL1right), rest671)
end
|  ( 110, ( ( _, ( MlyValue.LOWER_STRING_LITERAL LOWER_STRING_LITERAL1
, LOWER_STRING_LITERAL1left, LOWER_STRING_LITERAL1right)) :: rest671))
 => let val  result = MlyValue.name (fn _ => let val  (
LOWER_STRING_LITERAL as LOWER_STRING_LITERAL1) = LOWER_STRING_LITERAL1
 ()
 in (LOWER_STRING_LITERAL)
end)
 in ( LrTable.NT 1, ( result, LOWER_STRING_LITERAL1left, 
LOWER_STRING_LITERAL1right), rest671)
end
|  ( 111, ( ( _, ( MlyValue.UPPER_STRING_LITERAL UPPER_STRING_LITERAL1
, UPPER_STRING_LITERAL1left, UPPER_STRING_LITERAL1right)) :: rest671))
 => let val  result = MlyValue.uident (fn _ => let val  (
UPPER_STRING_LITERAL as UPPER_STRING_LITERAL1) = UPPER_STRING_LITERAL1
 ()
 in (UPPER_STRING_LITERAL)
end)
 in ( LrTable.NT 3, ( result, UPPER_STRING_LITERAL1left, 
UPPER_STRING_LITERAL1right), rest671)
end
|  ( 112, ( ( _, ( MlyValue.LOWER_STRING_LITERAL LOWER_STRING_LITERAL1
, LOWER_STRING_LITERAL1left, LOWER_STRING_LITERAL1right)) :: rest671))
 => let val  result = MlyValue.lident (fn _ => let val  (
LOWER_STRING_LITERAL as LOWER_STRING_LITERAL1) = LOWER_STRING_LITERAL1
 ()
 in (LOWER_STRING_LITERAL)
end)
 in ( LrTable.NT 4, ( result, LOWER_STRING_LITERAL1left, 
LOWER_STRING_LITERAL1right), rest671)
end
|  ( 113, ( ( _, ( MlyValue.lident lident1, lident1left, lident1right)
) :: rest671)) => let val  result = MlyValue.lidents (fn _ => let val 
 (lident as lident1) = lident1 ()
 in ([lident])
end)
 in ( LrTable.NT 12, ( result, lident1left, lident1right), rest671)

end
|  ( 114, ( ( _, ( MlyValue.lidents lidents1, _, lidents1right)) :: (
 _, ( MlyValue.COMMA COMMA1, _, _)) :: ( _, ( MlyValue.lident lident1,
 lident1left, _)) :: rest671)) => let val  result = MlyValue.lidents
 (fn _ => let val  (lident as lident1) = lident1 ()
 val  COMMA1 = COMMA1 ()
 val  (lidents as lidents1) = lidents1 ()
 in (lident::lidents)
end)
 in ( LrTable.NT 12, ( result, lident1left, lidents1right), rest671)

end
|  ( 115, ( ( _, ( MlyValue.uident uident1, uident1left, uident1right)
) :: rest671)) => let val  result = MlyValue.uidents (fn _ => let val 
 (uident as uident1) = uident1 ()
 in ([uident])
end)
 in ( LrTable.NT 13, ( result, uident1left, uident1right), rest671)

end
|  ( 116, ( ( _, ( MlyValue.uidents uidents1, _, uidents1right)) :: (
 _, ( MlyValue.COMMA COMMA1, _, _)) :: ( _, ( MlyValue.uident uident1,
 uident1left, _)) :: rest671)) => let val  result = MlyValue.uidents
 (fn _ => let val  (uident as uident1) = uident1 ()
 val  COMMA1 = COMMA1 ()
 val  (uidents as uidents1) = uidents1 ()
 in (uident::uidents)
end)
 in ( LrTable.NT 13, ( result, uident1left, uidents1right), rest671)

end
|  ( 117, ( ( _, ( MlyValue.uident uident1, uident1left, uident1right)
) :: rest671)) => let val  result = MlyValue.ident (fn _ => let val  (
uident as uident1) = uident1 ()
 in (uident)
end)
 in ( LrTable.NT 5, ( result, uident1left, uident1right), rest671)
end
|  ( 118, ( ( _, ( MlyValue.lident lident1, lident1left, lident1right)
) :: rest671)) => let val  result = MlyValue.ident (fn _ => let val  (
lident as lident1) = lident1 ()
 in (lident)
end)
 in ( LrTable.NT 5, ( result, lident1left, lident1right), rest671)
end
|  ( 119, ( ( _, ( MlyValue.INTEGER_LITERAL INTEGER_LITERAL1, 
INTEGER_LITERAL1left, INTEGER_LITERAL1right)) :: rest671)) => let val 
 result = MlyValue.arity (fn _ => let val  (INTEGER_LITERAL as 
INTEGER_LITERAL1) = INTEGER_LITERAL1 ()
 in (Option.valOf(Int.fromString(INTEGER_LITERAL)))
end)
 in ( LrTable.NT 2, ( result, INTEGER_LITERAL1left, 
INTEGER_LITERAL1right), rest671)
end
|  ( 120, ( ( _, ( MlyValue.CLOSESQB CLOSESQB1, _, CLOSESQB1right)) ::
 ( _, ( MlyValue.OPENSQB OPENSQB1, _, _)) :: ( _, ( MlyValue.EXCLAM 
EXCLAM1, _, _)) :: ( _, ( MlyValue.ident ident1, ident1left, _)) :: 
rest671)) => let val  result = MlyValue.abbrev_head (fn _ => let val 
 (ident as ident1) = ident1 ()
 val  EXCLAM1 = EXCLAM1 ()
 val  OPENSQB1 = OPENSQB1 ()
 val  CLOSESQB1 = CLOSESQB1 ()
 in ((ident,[]))
end)
 in ( LrTable.NT 50, ( result, ident1left, CLOSESQB1right), rest671)

end
|  ( 121, ( ( _, ( MlyValue.CLOSESQB CLOSESQB1, _, CLOSESQB1right)) ::
 ( _, ( MlyValue.uidents uidents1, _, _)) :: ( _, ( MlyValue.OPENSQB 
OPENSQB1, _, _)) :: ( _, ( MlyValue.EXCLAM EXCLAM1, _, _)) :: ( _, ( 
MlyValue.ident ident1, ident1left, _)) :: rest671)) => let val  result
 = MlyValue.abbrev_head (fn _ => let val  (ident as ident1) = ident1
 ()
 val  EXCLAM1 = EXCLAM1 ()
 val  OPENSQB1 = OPENSQB1 ()
 val  (uidents as uidents1) = uidents1 ()
 val  CLOSESQB1 = CLOSESQB1 ()
 in ((ident,uidents))
end)
 in ( LrTable.NT 50, ( result, ident1left, CLOSESQB1right), rest671)

end
|  ( 122, ( ( _, ( MlyValue.msg msg1, _, msg1right)) :: ( _, ( 
MlyValue.EQUAL EQUAL1, _, _)) :: ( _, ( MlyValue.abbrev_head 
abbrev_head1, abbrev_head1left, _)) :: rest671)) => let val  result = 
MlyValue.abbrev_decl (fn _ => let val  (abbrev_head as abbrev_head1) =
 abbrev_head1 ()
 val  EQUAL1 = EQUAL1 ()
 val  (msg as msg1) = msg1 ()
 in (TracProtocol.TermAbbreviation(abbrev_head,msg))
end)
 in ( LrTable.NT 51, ( result, abbrev_head1left, msg1right), rest671)

end
|  ( 123, ( ( _, ( MlyValue.DOT DOT1, _, DOT1right)) :: ( _, ( 
MlyValue.actions_ext actions_ext1, _, _)) :: ( _, ( 
MlyValue.abbrev_head abbrev_head1, abbrev_head1left, _)) :: rest671))
 => let val  result = MlyValue.abbrev_decl (fn _ => let val  (
abbrev_head as abbrev_head1) = abbrev_head1 ()
 val  (actions_ext as actions_ext1) = actions_ext1 ()
 val  DOT1 = DOT1 ()
 in (TracProtocol.ActionsAbbreviation(abbrev_head,actions_ext))
end)
 in ( LrTable.NT 51, ( result, abbrev_head1left, DOT1right), rest671)

end
|  ( 124, ( ( _, ( MlyValue.abbrev_decl abbrev_decl1, abbrev_decl1left
, abbrev_decl1right)) :: rest671)) => let val  result = 
MlyValue.abbrev_spec (fn _ => let val  (abbrev_decl as abbrev_decl1) =
 abbrev_decl1 ()
 in ([abbrev_decl])
end)
 in ( LrTable.NT 52, ( result, abbrev_decl1left, abbrev_decl1right), 
rest671)
end
|  ( 125, ( ( _, ( MlyValue.abbrev_spec abbrev_spec1, _, 
abbrev_spec1right)) :: ( _, ( MlyValue.abbrev_decl abbrev_decl1, 
abbrev_decl1left, _)) :: rest671)) => let val  result = 
MlyValue.abbrev_spec (fn _ => let val  (abbrev_decl as abbrev_decl1) =
 abbrev_decl1 ()
 val  (abbrev_spec as abbrev_spec1) = abbrev_spec1 ()
 in (abbrev_decl::abbrev_spec)
end)
 in ( LrTable.NT 52, ( result, abbrev_decl1left, abbrev_spec1right), 
rest671)
end
| _ => raise (mlyAction i392)
end
val void = MlyValue.VOID
val extract = fn a => (fn MlyValue.START x => x
| _ => let exception ParseInternal
	in raise ParseInternal end) a ()
end
end
structure Tokens : TracTransaction_TOKENS =
struct
type svalue = ParserData.svalue
type ('a,'b) token = ('a,'b) Token.token
fun EOF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 0,(
ParserData.MlyValue.VOID,p1,p2))
fun OPENP (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 1,(
ParserData.MlyValue.OPENP (fn () => i),p1,p2))
fun CLOSEP (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 2,(
ParserData.MlyValue.CLOSEP (fn () => i),p1,p2))
fun OPENB (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 3,(
ParserData.MlyValue.OPENB (fn () => i),p1,p2))
fun CLOSEB (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 4,(
ParserData.MlyValue.CLOSEB (fn () => i),p1,p2))
fun OPENSCRYPT (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 5,(
ParserData.MlyValue.OPENSCRYPT (fn () => i),p1,p2))
fun CLOSESCRYPT (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 6,(
ParserData.MlyValue.CLOSESCRYPT (fn () => i),p1,p2))
fun COLON (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 7,(
ParserData.MlyValue.COLON (fn () => i),p1,p2))
fun SEMICOLON (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 8,(
ParserData.MlyValue.SEMICOLON (fn () => i),p1,p2))
fun SECCH (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 9,(
ParserData.MlyValue.SECCH (fn () => i),p1,p2))
fun AUTHCH (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 10,(
ParserData.MlyValue.AUTHCH (fn () => i),p1,p2))
fun CONFCH (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 11,(
ParserData.MlyValue.CONFCH (fn () => i),p1,p2))
fun INSECCH (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 12,(
ParserData.MlyValue.INSECCH (fn () => i),p1,p2))
fun FAUTHCH (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 13,(
ParserData.MlyValue.FAUTHCH (fn () => i),p1,p2))
fun FSECCH (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 14,(
ParserData.MlyValue.FSECCH (fn () => i),p1,p2))
fun PERCENT (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 15,(
ParserData.MlyValue.PERCENT (fn () => i),p1,p2))
fun UNEQUAL (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 16,(
ParserData.MlyValue.UNEQUAL (fn () => i),p1,p2))
fun EXCLAM (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 17,(
ParserData.MlyValue.EXCLAM (fn () => i),p1,p2))
fun DOT (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 18,(
ParserData.MlyValue.DOT (fn () => i),p1,p2))
fun COMMA (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 19,(
ParserData.MlyValue.COMMA (fn () => i),p1,p2))
fun OPENSQB (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 20,(
ParserData.MlyValue.OPENSQB (fn () => i),p1,p2))
fun CLOSESQB (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 21,(
ParserData.MlyValue.CLOSESQB (fn () => i),p1,p2))
fun UNION (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 22,(
ParserData.MlyValue.UNION (fn () => i),p1,p2))
fun INFINITESET (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 23,(
ParserData.MlyValue.INFINITESET (fn () => i),p1,p2))
fun PROTOCOL (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 24,(
ParserData.MlyValue.PROTOCOL (fn () => i),p1,p2))
fun KNOWLEDGE (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 25,(
ParserData.MlyValue.KNOWLEDGE (fn () => i),p1,p2))
fun WHERE (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 26,(
ParserData.MlyValue.WHERE (fn () => i),p1,p2))
fun ACTIONS (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 27,(
ParserData.MlyValue.ACTIONS (fn () => i),p1,p2))
fun ABSTRACTION (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 28,(
ParserData.MlyValue.ABSTRACTION (fn () => i),p1,p2))
fun GOALS (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 29,(
ParserData.MlyValue.GOALS (fn () => i),p1,p2))
fun AUTHENTICATES (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 30,(
ParserData.MlyValue.AUTHENTICATES (fn () => i),p1,p2))
fun WEAKLY (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 31,(
ParserData.MlyValue.WEAKLY (fn () => i),p1,p2))
fun ON (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 32,(
ParserData.MlyValue.ON (fn () => i),p1,p2))
fun TSECRET (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 33,(
ParserData.MlyValue.TSECRET (fn () => i),p1,p2))
fun TBETWEEN (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 34,(
ParserData.MlyValue.TBETWEEN (fn () => i),p1,p2))
fun Sets (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 35,(
ParserData.MlyValue.Sets (fn () => i),p1,p2))
fun FUNCTIONS (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 36,(
ParserData.MlyValue.FUNCTIONS (fn () => i),p1,p2))
fun PUBLIC (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 37,(
ParserData.MlyValue.PUBLIC (fn () => i),p1,p2))
fun PRIVATE (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 38,(
ParserData.MlyValue.PRIVATE (fn () => i),p1,p2))
fun RECEIVE (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 39,(
ParserData.MlyValue.RECEIVE (fn () => i),p1,p2))
fun SEND (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 40,(
ParserData.MlyValue.SEND (fn () => i),p1,p2))
fun LET (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 41,(
ParserData.MlyValue.LET (fn () => i),p1,p2))
fun IN (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 42,(
ParserData.MlyValue.IN (fn () => i),p1,p2))
fun NOTIN (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 43,(
ParserData.MlyValue.NOTIN (fn () => i),p1,p2))
fun INSERT (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 44,(
ParserData.MlyValue.INSERT (fn () => i),p1,p2))
fun DELETE (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 45,(
ParserData.MlyValue.DELETE (fn () => i),p1,p2))
fun NEW (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 46,(
ParserData.MlyValue.NEW (fn () => i),p1,p2))
fun ATTACK (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 47,(
ParserData.MlyValue.ATTACK (fn () => i),p1,p2))
fun SLASH (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 48,(
ParserData.MlyValue.SLASH (fn () => i),p1,p2))
fun DOUBLESLASH (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 49,(
ParserData.MlyValue.DOUBLESLASH (fn () => i),p1,p2))
fun QUESTION (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 50,(
ParserData.MlyValue.QUESTION (fn () => i),p1,p2))
fun EQUAL (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 51,(
ParserData.MlyValue.EQUAL (fn () => i),p1,p2))
fun DOUBLEEQUAL (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 52,(
ParserData.MlyValue.DOUBLEEQUAL (fn () => i),p1,p2))
fun TYPES (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 53,(
ParserData.MlyValue.TYPES (fn () => i),p1,p2))
fun ENUMERATIONS (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 54,(
ParserData.MlyValue.ENUMERATIONS (fn () => i),p1,p2))
fun SETS (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 55,(
ParserData.MlyValue.SETS (fn () => i),p1,p2))
fun ARROW (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 56,(
ParserData.MlyValue.ARROW (fn () => i),p1,p2))
fun ANALYSIS (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 57,(
ParserData.MlyValue.ANALYSIS (fn () => i),p1,p2))
fun TRANSACTIONS (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 58,(
ParserData.MlyValue.TRANSACTIONS (fn () => i),p1,p2))
fun ABBREVIATIONS (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 59,(
ParserData.MlyValue.ABBREVIATIONS (fn () => i),p1,p2))
fun STRING_LITERAL (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 60,(
ParserData.MlyValue.STRING_LITERAL (fn () => i),p1,p2))
fun UPPER_STRING_LITERAL (i,p1,p2) = Token.TOKEN (
ParserData.LrTable.T 61,(ParserData.MlyValue.UPPER_STRING_LITERAL
 (fn () => i),p1,p2))
fun LOWER_STRING_LITERAL (i,p1,p2) = Token.TOKEN (
ParserData.LrTable.T 62,(ParserData.MlyValue.LOWER_STRING_LITERAL
 (fn () => i),p1,p2))
fun UNDERSCORE (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 63,(
ParserData.MlyValue.UNDERSCORE (fn () => i),p1,p2))
fun INTEGER_LITERAL (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 64,(
ParserData.MlyValue.INTEGER_LITERAL (fn () => i),p1,p2))
fun STAR (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 65,(
ParserData.MlyValue.STAR (fn () => i),p1,p2))
fun OF (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 66,(
ParserData.MlyValue.OF (fn () => i),p1,p2))
fun OR (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 67,(
ParserData.MlyValue.OR (fn () => i),p1,p2))
fun FORALL (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 68,(
ParserData.MlyValue.FORALL (fn () => i),p1,p2))
end
end
