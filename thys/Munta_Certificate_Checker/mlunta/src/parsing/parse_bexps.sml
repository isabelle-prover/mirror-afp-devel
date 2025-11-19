signature PARSE_BEXPS = sig
    val edge: ParseJsonTypes.edge -> ParseBexpTypes.edge Error.res
    val node: ParseJsonTypes.node -> ParseBexpTypes.node Error.res
    val network: ParseJsonTypes.network -> ParseBexpTypes.network Error.res
end

structure ParseBexps : PARSE_BEXPS = struct
open Either
open ParseJsonTypes

fun edge ({source, target, guard, label, update} : edge) =
    (BexpParser.guard guard <|> BexpParser.action label
    <|> BexpParser.updates update)
    |> mapR (fn ((g,l),upd) =>
                {
                  source = source,
                  target = target,
                  guard = g,
                  label = l,
                  update = upd})

fun node ({ id: int, name: string, invar: string } : node) =
    BexpParser.invariant invar
    |> mapR (fn invar' => {id = id, name = name, invariant = invar'})

fun automaton ({ nodes, edges, initial, committed} : automaton) =
    (combine_map node nodes <|> combine_map edge edges)
    |> mapR (fn (V,E) =>
                {
                  nodes = V,
                  edges = E,
                  initial = initial,
                  committed = committed
            })

fun network ( { automata, clocks, vars,
                formula, broadcast_channels } : network) =
    (combine_map (fn (s,ta) => automaton ta |> mapR (pair s)) automata
    <|> BexpParser.clocks clocks
    <|> BexpParser.vars vars
    <|> BexpParser.formula formula
    <|> combine_map BexpParser.broadcast broadcast_channels)
    |> mapR
    (fn ((((tas,clocks), vars), formula), broadcast_channels)
        => {
         automata = tas,
         vars = vars,
         clocks = clocks,
         formula = formula,
         broadcast_channels = broadcast_channels
    })
end
