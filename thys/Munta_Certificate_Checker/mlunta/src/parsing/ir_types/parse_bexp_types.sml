structure ParseBexpTypes = struct
    type node = {
        id: int,
        name: string,
        invariant: (string, int) Syntax.invariant
    }


    type edge = {
        source: int,
        target: int,
        guard: (string, int) Syntax.guard,
        label: string Syntax.action,
        update: string Syntax.update list
    }


    type automaton = {
        nodes: node list,
        edges: edge list,
        initial: int,
        committed: int list
    }


    type network = {
        automata: (string * automaton) list,
        clocks: string list,
        vars: Syntax.var list,
        formula: (string, int) Syntax.formula,
        broadcast_channels: string list
    }
end
