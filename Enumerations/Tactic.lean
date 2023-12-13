macro "transform" f:term " => " cs:Lean.Parser.Tactic.Conv.convSeq : tactic => do
  `(tactic| (
      have eq : $f = $f := rfl
      conv at eq =>
        rhs
        ($cs)
      exact eq))
