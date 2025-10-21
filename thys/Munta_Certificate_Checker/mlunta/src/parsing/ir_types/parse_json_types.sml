structure ParseJsonTypes = struct
type node = {
  id: int,
  name: string,
  invar: string
}

type edge = {
  source: int,
  target: int,
  guard: string,
  label: string,
  update: string
}

type automaton = {
  nodes: node list,
  edges: edge list,
  committed: int list,
  initial: int
}

type network = {
  automata: (string * automaton) list,
  broadcast_channels: string list,
  clocks: string,
  vars: string,
  formula: string
}
end
