signature SCANNER_COMB = sig
  val infix_pairc: 'a Symbol.parser -> 'b Symbol.parser -> Symbol.symbol
                   -> ('a * 'b -> 'c) -> 'c Symbol.parser
  val single_c: 'a Symbol.parser -> Symbol.symbol -> ('a -> 'b)
                -> 'b Symbol.parser
  val body: Symbol.symbol -> Symbol.symbol -> Symbol.symbol ->
            'a Symbol.parser ->
            'a list Symbol.parser
  val infix_collection: Symbol.symbol -> 'a Symbol.parser
                        -> 'a list Symbol.parser
end

structure ScannerCombinator : SCANNER_COMB = struct
fun infix_pairc p1 p2 sep c =
    (p1 --| Symbol.strip_whitespace (Scan.this_string sep) -- p2) >> c

fun single_c p hd c =
    Symbol.strip_whitespace (Scan.this_string hd) |-- p >> c

local open Symbol in
fun body lhs rhs sep (p : 'a Symbol.parser) =
    strip_whitespace (Scan.this_string lhs) |-- (
      (p -- (Scan.repeat (strip_whitespace ($$ sep) -- p >> snd))
                         >> op ::)
      || Scan.succeed []
    ) --| strip_whitespace (Scan.this_string rhs)


fun infix_collection sep p =
    (p -- (Scan.repeat (strip_whitespace ($$ sep) -- p >> snd))
       >> op ::)
    || Scan.succeed []
end
end
